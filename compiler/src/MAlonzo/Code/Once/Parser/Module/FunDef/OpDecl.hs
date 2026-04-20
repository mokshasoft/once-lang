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
import qualified MAlonzo.Code.Once.Parser.PolyType
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core
import qualified MAlonzo.Code.Relation.Nullary.Reflects

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
                           = MAlonzo.Code.Once.Parser.PolyType.d_parsePolyAtomImpl_30
                               (coe v4) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> case coe v6 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                   -> let v9
                                            = MAlonzo.Code.Once.Parser.PolyType.d_parsePolyProdTail_36
                                                (coe v7) (coe v8) in
                                      coe
                                        (case coe v9 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                             -> case coe v10 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                    -> let v13
                                                             = MAlonzo.Code.Once.Parser.PolyType.d_parsePolySumTail_34
                                                                 (coe v11) (coe v12) in
                                                       coe
                                                         (case coe v13 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                              -> case coe v14 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                     -> let v17
                                                                              = MAlonzo.Code.Once.Parser.PolyType.d_parsePolyArrowTail_32
                                                                                  (coe v15)
                                                                                  (coe v16) in
                                                                        coe
                                                                          (case coe v17 of
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                               -> case coe v18 of
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                                                      -> let v21
                                                                                               = coe
                                                                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                   (\ v21 ->
                                                                                                      coe
                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                                                        (coe
                                                                                                           addInt
                                                                                                           (coe
                                                                                                              (1 ::
                                                                                                                 Integer))
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                              v20)))
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                                                   (coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                                                         (coe
                                                                                                            addInt
                                                                                                            (coe
                                                                                                               (1 ::
                                                                                                                  Integer))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                               v20))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                            v4))) in
                                                                                         coe
                                                                                           (case coe
                                                                                                   v21 of
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                -> if coe
                                                                                                        v22
                                                                                                     then case coe
                                                                                                                 v23 of
                                                                                                            MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v24
                                                                                                              -> coe
                                                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                         (coe
                                                                                                                            v0)
                                                                                                                         (coe
                                                                                                                            v19))
                                                                                                                      (coe
                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                         (coe
                                                                                                                            v20)
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                            (coe
                                                                                                                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                  (coe
                                                                                                                                     (\ v25
                                                                                                                                        v26 ->
                                                                                                                                        addInt
                                                                                                                                          (coe
                                                                                                                                             (1 ::
                                                                                                                                                Integer))
                                                                                                                                          (coe
                                                                                                                                             v26)))
                                                                                                                                  (coe
                                                                                                                                     (0 ::
                                                                                                                                        Integer))
                                                                                                                                  (coe
                                                                                                                                     v4))
                                                                                                                               (coe
                                                                                                                                  v24)
                                                                                                                               (coe
                                                                                                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                  (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                     (coe
                                                                                                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                        (coe
                                                                                                                                           (\ v25
                                                                                                                                              v26 ->
                                                                                                                                              addInt
                                                                                                                                                (coe
                                                                                                                                                   (1 ::
                                                                                                                                                      Integer))
                                                                                                                                                (coe
                                                                                                                                                   v26)))
                                                                                                                                        (coe
                                                                                                                                           (0 ::
                                                                                                                                              Integer))
                                                                                                                                        (coe
                                                                                                                                           v4))))))))
                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                     else (let v24
                                                                                                                 = seq
                                                                                                                     (coe
                                                                                                                        v23)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18) in
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
                                                                                                                                           MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                                           (coe
                                                                                                                                              v0)
                                                                                                                                           (coe
                                                                                                                                              v26))
                                                                                                                                        (coe
                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                           (coe
                                                                                                                                              v28)
                                                                                                                                           (coe
                                                                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                                    (coe
                                                                                                                                                       (\ v30
                                                                                                                                                          v31 ->
                                                                                                                                                          addInt
                                                                                                                                                            (coe
                                                                                                                                                               (1 ::
                                                                                                                                                                  Integer))
                                                                                                                                                            (coe
                                                                                                                                                               v31)))
                                                                                                                                                    (coe
                                                                                                                                                       (0 ::
                                                                                                                                                          Integer))
                                                                                                                                                    (coe
                                                                                                                                                       v4))
                                                                                                                                                 (coe
                                                                                                                                                    v29)
                                                                                                                                                 (coe
                                                                                                                                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                                       (coe
                                                                                                                                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                                          (coe
                                                                                                                                                             (\ v30
                                                                                                                                                                v31 ->
                                                                                                                                                                addInt
                                                                                                                                                                  (coe
                                                                                                                                                                     (1 ::
                                                                                                                                                                        Integer))
                                                                                                                                                                  (coe
                                                                                                                                                                     v31)))
                                                                                                                                                          (coe
                                                                                                                                                             (0 ::
                                                                                                                                                                Integer))
                                                                                                                                                          (coe
                                                                                                                                                             v4))))))))
                                                                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                                  -> coe
                                                                                                                       v24
                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                              _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                               -> case coe v17 of
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
                                                                                                               MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                               (coe
                                                                                                                  v0)
                                                                                                               (coe
                                                                                                                  v19))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v21)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                        (coe
                                                                                                                           (\ v23
                                                                                                                              v24 ->
                                                                                                                              addInt
                                                                                                                                (coe
                                                                                                                                   (1 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   v24)))
                                                                                                                        (coe
                                                                                                                           (0 ::
                                                                                                                              Integer))
                                                                                                                        (coe
                                                                                                                           v4))
                                                                                                                     (coe
                                                                                                                        v22)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                        (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                              (coe
                                                                                                                                 (\ v23
                                                                                                                                    v24 ->
                                                                                                                                    addInt
                                                                                                                                      (coe
                                                                                                                                         (1 ::
                                                                                                                                            Integer))
                                                                                                                                      (coe
                                                                                                                                         v24)))
                                                                                                                              (coe
                                                                                                                                 (0 ::
                                                                                                                                    Integer))
                                                                                                                              (coe
                                                                                                                                 v4))))))))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                      -> coe v17
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> case coe v13 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> let v17
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                         (\ v17 ->
                                                                                            coe
                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                                              (coe
                                                                                                 addInt
                                                                                                 (coe
                                                                                                    (1 ::
                                                                                                       Integer))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                    v16)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                                               (coe
                                                                                                  addInt
                                                                                                  (coe
                                                                                                     (1 ::
                                                                                                        Integer))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                     v16))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                  v4))) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                      -> if coe v18
                                                                                           then case coe
                                                                                                       v19 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                               (coe
                                                                                                                  v0)
                                                                                                               (coe
                                                                                                                  v15))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v16)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                        (coe
                                                                                                                           (\ v21
                                                                                                                              v22 ->
                                                                                                                              addInt
                                                                                                                                (coe
                                                                                                                                   (1 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   v22)))
                                                                                                                        (coe
                                                                                                                           (0 ::
                                                                                                                              Integer))
                                                                                                                        (coe
                                                                                                                           v4))
                                                                                                                     (coe
                                                                                                                        v20)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                        (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                              (coe
                                                                                                                                 (\ v21
                                                                                                                                    v22 ->
                                                                                                                                    addInt
                                                                                                                                      (coe
                                                                                                                                         (1 ::
                                                                                                                                            Integer))
                                                                                                                                      (coe
                                                                                                                                         v22)))
                                                                                                                              (coe
                                                                                                                                 (0 ::
                                                                                                                                    Integer))
                                                                                                                              (coe
                                                                                                                                 v4))))))))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           else (let v20
                                                                                                       = seq
                                                                                                           (coe
                                                                                                              v19)
                                                                                                           (coe
                                                                                                              v13) in
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
                                                                                                                                 MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                                 (coe
                                                                                                                                    v0)
                                                                                                                                 (coe
                                                                                                                                    v22))
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                 (coe
                                                                                                                                    v24)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                          (coe
                                                                                                                                             (\ v26
                                                                                                                                                v27 ->
                                                                                                                                                addInt
                                                                                                                                                  (coe
                                                                                                                                                     (1 ::
                                                                                                                                                        Integer))
                                                                                                                                                  (coe
                                                                                                                                                     v27)))
                                                                                                                                          (coe
                                                                                                                                             (0 ::
                                                                                                                                                Integer))
                                                                                                                                          (coe
                                                                                                                                             v4))
                                                                                                                                       (coe
                                                                                                                                          v25)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                                (coe
                                                                                                                                                   (\ v26
                                                                                                                                                      v27 ->
                                                                                                                                                      addInt
                                                                                                                                                        (coe
                                                                                                                                                           (1 ::
                                                                                                                                                              Integer))
                                                                                                                                                        (coe
                                                                                                                                                           v27)))
                                                                                                                                                (coe
                                                                                                                                                   (0 ::
                                                                                                                                                      Integer))
                                                                                                                                                (coe
                                                                                                                                                   v4))))))))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                        -> coe
                                                                                                             v20
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> case coe v13 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                            -> case coe v14 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                   -> case coe
                                                                                             v16 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v15))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        v17)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                              (coe
                                                                                                                 (\ v19
                                                                                                                    v20 ->
                                                                                                                    addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v20)))
                                                                                                              (coe
                                                                                                                 (0 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v4))
                                                                                                           (coe
                                                                                                              v18)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                    (coe
                                                                                                                       (\ v19
                                                                                                                          v20 ->
                                                                                                                          addInt
                                                                                                                            (coe
                                                                                                                               (1 ::
                                                                                                                                  Integer))
                                                                                                                            (coe
                                                                                                                               v20)))
                                                                                                                    (coe
                                                                                                                       (0 ::
                                                                                                                          Integer))
                                                                                                                    (coe
                                                                                                                       v4))))))))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                            -> coe v13
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                           -> let v13
                                                                    = MAlonzo.Code.Once.Parser.PolyType.d_parsePolyArrowTail_32
                                                                        (coe v11) (coe v12) in
                                                              coe
                                                                (case coe v13 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> let v17
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                         (\ v17 ->
                                                                                            coe
                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                                              (coe
                                                                                                 addInt
                                                                                                 (coe
                                                                                                    (1 ::
                                                                                                       Integer))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                    v16)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                                               (coe
                                                                                                  addInt
                                                                                                  (coe
                                                                                                     (1 ::
                                                                                                        Integer))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                     v16))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                  v4))) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                      -> if coe v18
                                                                                           then case coe
                                                                                                       v19 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                               (coe
                                                                                                                  v0)
                                                                                                               (coe
                                                                                                                  v15))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v16)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                        (coe
                                                                                                                           (\ v21
                                                                                                                              v22 ->
                                                                                                                              addInt
                                                                                                                                (coe
                                                                                                                                   (1 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   v22)))
                                                                                                                        (coe
                                                                                                                           (0 ::
                                                                                                                              Integer))
                                                                                                                        (coe
                                                                                                                           v4))
                                                                                                                     (coe
                                                                                                                        v20)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                        (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                              (coe
                                                                                                                                 (\ v21
                                                                                                                                    v22 ->
                                                                                                                                    addInt
                                                                                                                                      (coe
                                                                                                                                         (1 ::
                                                                                                                                            Integer))
                                                                                                                                      (coe
                                                                                                                                         v22)))
                                                                                                                              (coe
                                                                                                                                 (0 ::
                                                                                                                                    Integer))
                                                                                                                              (coe
                                                                                                                                 v4))))))))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           else (let v20
                                                                                                       = seq
                                                                                                           (coe
                                                                                                              v19)
                                                                                                           (coe
                                                                                                              v9) in
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
                                                                                                                                 MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                                 (coe
                                                                                                                                    v0)
                                                                                                                                 (coe
                                                                                                                                    v22))
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                 (coe
                                                                                                                                    v24)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                          (coe
                                                                                                                                             (\ v26
                                                                                                                                                v27 ->
                                                                                                                                                addInt
                                                                                                                                                  (coe
                                                                                                                                                     (1 ::
                                                                                                                                                        Integer))
                                                                                                                                                  (coe
                                                                                                                                                     v27)))
                                                                                                                                          (coe
                                                                                                                                             (0 ::
                                                                                                                                                Integer))
                                                                                                                                          (coe
                                                                                                                                             v4))
                                                                                                                                       (coe
                                                                                                                                          v25)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                                (coe
                                                                                                                                                   (\ v26
                                                                                                                                                      v27 ->
                                                                                                                                                      addInt
                                                                                                                                                        (coe
                                                                                                                                                           (1 ::
                                                                                                                                                              Integer))
                                                                                                                                                        (coe
                                                                                                                                                           v27)))
                                                                                                                                                (coe
                                                                                                                                                   (0 ::
                                                                                                                                                      Integer))
                                                                                                                                                (coe
                                                                                                                                                   v4))))))))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                        -> coe
                                                                                                             v20
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> case coe v13 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                            -> case coe v14 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                   -> case coe
                                                                                             v16 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v15))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        v17)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                              (coe
                                                                                                                 (\ v19
                                                                                                                    v20 ->
                                                                                                                    addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v20)))
                                                                                                              (coe
                                                                                                                 (0 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v4))
                                                                                                           (coe
                                                                                                              v18)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                    (coe
                                                                                                                       (\ v19
                                                                                                                          v20 ->
                                                                                                                          addInt
                                                                                                                            (coe
                                                                                                                               (1 ::
                                                                                                                                  Integer))
                                                                                                                            (coe
                                                                                                                               v20)))
                                                                                                                    (coe
                                                                                                                       (0 ::
                                                                                                                          Integer))
                                                                                                                    (coe
                                                                                                                       v4))))))))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                            -> coe v13
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                  -> let v13
                                                                           = coe
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                               (\ v13 ->
                                                                                  coe
                                                                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Base.du_length_268
                                                                                          v12)))
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                                     (coe
                                                                                        addInt
                                                                                        (coe
                                                                                           (1 ::
                                                                                              Integer))
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.List.Base.du_length_268
                                                                                           v12))
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.List.Base.du_length_268
                                                                                        v4))) in
                                                                     coe
                                                                       (case coe v13 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                            -> if coe v14
                                                                                 then case coe
                                                                                             v15 of
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v11))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        v12)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                              (coe
                                                                                                                 (\ v17
                                                                                                                    v18 ->
                                                                                                                    addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v18)))
                                                                                                              (coe
                                                                                                                 (0 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v4))
                                                                                                           (coe
                                                                                                              v16)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                    (coe
                                                                                                                       (\ v17
                                                                                                                          v18 ->
                                                                                                                          addInt
                                                                                                                            (coe
                                                                                                                               (1 ::
                                                                                                                                  Integer))
                                                                                                                            (coe
                                                                                                                               v18)))
                                                                                                                    (coe
                                                                                                                       (0 ::
                                                                                                                          Integer))
                                                                                                                    (coe
                                                                                                                       v4))))))))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 else (let v16
                                                                                             = seq
                                                                                                 (coe
                                                                                                    v15)
                                                                                                 (coe
                                                                                                    v9) in
                                                                                       coe
                                                                                         (case coe
                                                                                                 v16 of
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                                              -> case coe
                                                                                                        v17 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                                     -> case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                            -> coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                       (coe
                                                                                                                          v0)
                                                                                                                       (coe
                                                                                                                          v18))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                       (coe
                                                                                                                          v20)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                (coe
                                                                                                                                   (\ v22
                                                                                                                                      v23 ->
                                                                                                                                      addInt
                                                                                                                                        (coe
                                                                                                                                           (1 ::
                                                                                                                                              Integer))
                                                                                                                                        (coe
                                                                                                                                           v23)))
                                                                                                                                (coe
                                                                                                                                   (0 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   v4))
                                                                                                                             (coe
                                                                                                                                v21)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                      (coe
                                                                                                                                         (\ v22
                                                                                                                                            v23 ->
                                                                                                                                            addInt
                                                                                                                                              (coe
                                                                                                                                                 (1 ::
                                                                                                                                                    Integer))
                                                                                                                                              (coe
                                                                                                                                                 v23)))
                                                                                                                                      (coe
                                                                                                                                         (0 ::
                                                                                                                                            Integer))
                                                                                                                                      (coe
                                                                                                                                         v4))))))))
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                              -> coe
                                                                                                   v16
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
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
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v11))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v13)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
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
                                                                                                       v4))
                                                                                                 (coe
                                                                                                    v14)
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
                                                                                                             v4))))))))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe v9
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> case coe v5 of
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                   -> case coe v6 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                          -> let v9
                                                   = MAlonzo.Code.Once.Parser.PolyType.d_parsePolySumTail_34
                                                       (coe v7) (coe v8) in
                                             coe
                                               (case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                           -> let v13
                                                                    = MAlonzo.Code.Once.Parser.PolyType.d_parsePolyArrowTail_32
                                                                        (coe v11) (coe v12) in
                                                              coe
                                                                (case coe v13 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> let v17
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                         (\ v17 ->
                                                                                            coe
                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                                              (coe
                                                                                                 addInt
                                                                                                 (coe
                                                                                                    (1 ::
                                                                                                       Integer))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                    v16)))
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                                         (coe
                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                            (coe
                                                                                               MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                                               (coe
                                                                                                  addInt
                                                                                                  (coe
                                                                                                     (1 ::
                                                                                                        Integer))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                     v16))
                                                                                               (coe
                                                                                                  MAlonzo.Code.Data.List.Base.du_length_268
                                                                                                  v4))) in
                                                                               coe
                                                                                 (case coe v17 of
                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                      -> if coe v18
                                                                                           then case coe
                                                                                                       v19 of
                                                                                                  MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v20
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                               (coe
                                                                                                                  v0)
                                                                                                               (coe
                                                                                                                  v15))
                                                                                                            (coe
                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                               (coe
                                                                                                                  v16)
                                                                                                               (coe
                                                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                        (coe
                                                                                                                           (\ v21
                                                                                                                              v22 ->
                                                                                                                              addInt
                                                                                                                                (coe
                                                                                                                                   (1 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   v22)))
                                                                                                                        (coe
                                                                                                                           (0 ::
                                                                                                                              Integer))
                                                                                                                        (coe
                                                                                                                           v4))
                                                                                                                     (coe
                                                                                                                        v20)
                                                                                                                     (coe
                                                                                                                        MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                        (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                              (coe
                                                                                                                                 (\ v21
                                                                                                                                    v22 ->
                                                                                                                                    addInt
                                                                                                                                      (coe
                                                                                                                                         (1 ::
                                                                                                                                            Integer))
                                                                                                                                      (coe
                                                                                                                                         v22)))
                                                                                                                              (coe
                                                                                                                                 (0 ::
                                                                                                                                    Integer))
                                                                                                                              (coe
                                                                                                                                 v4))))))))
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                                           else (let v20
                                                                                                       = seq
                                                                                                           (coe
                                                                                                              v19)
                                                                                                           (coe
                                                                                                              v5) in
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
                                                                                                                                 MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                                 (coe
                                                                                                                                    v0)
                                                                                                                                 (coe
                                                                                                                                    v22))
                                                                                                                              (coe
                                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                 (coe
                                                                                                                                    v24)
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                                    (coe
                                                                                                                                       MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                          (coe
                                                                                                                                             (\ v26
                                                                                                                                                v27 ->
                                                                                                                                                addInt
                                                                                                                                                  (coe
                                                                                                                                                     (1 ::
                                                                                                                                                        Integer))
                                                                                                                                                  (coe
                                                                                                                                                     v27)))
                                                                                                                                          (coe
                                                                                                                                             (0 ::
                                                                                                                                                Integer))
                                                                                                                                          (coe
                                                                                                                                             v4))
                                                                                                                                       (coe
                                                                                                                                          v25)
                                                                                                                                       (coe
                                                                                                                                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                                (coe
                                                                                                                                                   (\ v26
                                                                                                                                                      v27 ->
                                                                                                                                                      addInt
                                                                                                                                                        (coe
                                                                                                                                                           (1 ::
                                                                                                                                                              Integer))
                                                                                                                                                        (coe
                                                                                                                                                           v27)))
                                                                                                                                                (coe
                                                                                                                                                   (0 ::
                                                                                                                                                      Integer))
                                                                                                                                                (coe
                                                                                                                                                   v4))))))))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                                        -> coe
                                                                                                             v20
                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError)
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> case coe v13 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v14
                                                                            -> case coe v14 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                   -> case coe
                                                                                             v16 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v15))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        v17)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                              (coe
                                                                                                                 (\ v19
                                                                                                                    v20 ->
                                                                                                                    addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v20)))
                                                                                                              (coe
                                                                                                                 (0 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v4))
                                                                                                           (coe
                                                                                                              v18)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                    (coe
                                                                                                                       (\ v19
                                                                                                                          v20 ->
                                                                                                                          addInt
                                                                                                                            (coe
                                                                                                                               (1 ::
                                                                                                                                  Integer))
                                                                                                                            (coe
                                                                                                                               v20)))
                                                                                                                    (coe
                                                                                                                       (0 ::
                                                                                                                          Integer))
                                                                                                                    (coe
                                                                                                                       v4))))))))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                            -> coe v13
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                  -> let v13
                                                                           = coe
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                               (\ v13 ->
                                                                                  coe
                                                                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Base.du_length_268
                                                                                          v12)))
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                                     (coe
                                                                                        addInt
                                                                                        (coe
                                                                                           (1 ::
                                                                                              Integer))
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.List.Base.du_length_268
                                                                                           v12))
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.List.Base.du_length_268
                                                                                        v4))) in
                                                                     coe
                                                                       (case coe v13 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                            -> if coe v14
                                                                                 then case coe
                                                                                             v15 of
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v11))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        v12)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                              (coe
                                                                                                                 (\ v17
                                                                                                                    v18 ->
                                                                                                                    addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v18)))
                                                                                                              (coe
                                                                                                                 (0 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v4))
                                                                                                           (coe
                                                                                                              v16)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                    (coe
                                                                                                                       (\ v17
                                                                                                                          v18 ->
                                                                                                                          addInt
                                                                                                                            (coe
                                                                                                                               (1 ::
                                                                                                                                  Integer))
                                                                                                                            (coe
                                                                                                                               v18)))
                                                                                                                    (coe
                                                                                                                       (0 ::
                                                                                                                          Integer))
                                                                                                                    (coe
                                                                                                                       v4))))))))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 else (let v16
                                                                                             = seq
                                                                                                 (coe
                                                                                                    v15)
                                                                                                 (coe
                                                                                                    v9) in
                                                                                       coe
                                                                                         (case coe
                                                                                                 v16 of
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                                              -> case coe
                                                                                                        v17 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                                     -> case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                            -> coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                       (coe
                                                                                                                          v0)
                                                                                                                       (coe
                                                                                                                          v18))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                       (coe
                                                                                                                          v20)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                (coe
                                                                                                                                   (\ v22
                                                                                                                                      v23 ->
                                                                                                                                      addInt
                                                                                                                                        (coe
                                                                                                                                           (1 ::
                                                                                                                                              Integer))
                                                                                                                                        (coe
                                                                                                                                           v23)))
                                                                                                                                (coe
                                                                                                                                   (0 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   v4))
                                                                                                                             (coe
                                                                                                                                v21)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                      (coe
                                                                                                                                         (\ v22
                                                                                                                                            v23 ->
                                                                                                                                            addInt
                                                                                                                                              (coe
                                                                                                                                                 (1 ::
                                                                                                                                                    Integer))
                                                                                                                                              (coe
                                                                                                                                                 v23)))
                                                                                                                                      (coe
                                                                                                                                         (0 ::
                                                                                                                                            Integer))
                                                                                                                                      (coe
                                                                                                                                         v4))))))))
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                              -> coe
                                                                                                   v16
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
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
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v11))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v13)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
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
                                                                                                       v4))
                                                                                                 (coe
                                                                                                    v14)
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
                                                                                                             v4))))))))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe v9
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                   -> case coe v5 of
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                          -> case coe v6 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                 -> let v9
                                                          = MAlonzo.Code.Once.Parser.PolyType.d_parsePolyArrowTail_32
                                                              (coe v7) (coe v8) in
                                                    coe
                                                      (case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                           -> case coe v10 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                                  -> let v13
                                                                           = coe
                                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                               (\ v13 ->
                                                                                  coe
                                                                                    MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                                    (coe
                                                                                       addInt
                                                                                       (coe
                                                                                          (1 ::
                                                                                             Integer))
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.List.Base.du_length_268
                                                                                          v12)))
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                               (coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                                     (coe
                                                                                        addInt
                                                                                        (coe
                                                                                           (1 ::
                                                                                              Integer))
                                                                                        (coe
                                                                                           MAlonzo.Code.Data.List.Base.du_length_268
                                                                                           v12))
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.List.Base.du_length_268
                                                                                        v4))) in
                                                                     coe
                                                                       (case coe v13 of
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                            -> if coe v14
                                                                                 then case coe
                                                                                             v15 of
                                                                                        MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v16
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                     (coe
                                                                                                        v0)
                                                                                                     (coe
                                                                                                        v11))
                                                                                                  (coe
                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                     (coe
                                                                                                        v12)
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                        (coe
                                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                              (coe
                                                                                                                 (\ v17
                                                                                                                    v18 ->
                                                                                                                    addInt
                                                                                                                      (coe
                                                                                                                         (1 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v18)))
                                                                                                              (coe
                                                                                                                 (0 ::
                                                                                                                    Integer))
                                                                                                              (coe
                                                                                                                 v4))
                                                                                                           (coe
                                                                                                              v16)
                                                                                                           (coe
                                                                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                              (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                    (coe
                                                                                                                       (\ v17
                                                                                                                          v18 ->
                                                                                                                          addInt
                                                                                                                            (coe
                                                                                                                               (1 ::
                                                                                                                                  Integer))
                                                                                                                            (coe
                                                                                                                               v18)))
                                                                                                                    (coe
                                                                                                                       (0 ::
                                                                                                                          Integer))
                                                                                                                    (coe
                                                                                                                       v4))))))))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 else (let v16
                                                                                             = seq
                                                                                                 (coe
                                                                                                    v15)
                                                                                                 (coe
                                                                                                    v5) in
                                                                                       coe
                                                                                         (case coe
                                                                                                 v16 of
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                                              -> case coe
                                                                                                        v17 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                                     -> case coe
                                                                                                               v19 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                                            -> coe
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                                       (coe
                                                                                                                          v0)
                                                                                                                       (coe
                                                                                                                          v18))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                       (coe
                                                                                                                          v20)
                                                                                                                       (coe
                                                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                (coe
                                                                                                                                   (\ v22
                                                                                                                                      v23 ->
                                                                                                                                      addInt
                                                                                                                                        (coe
                                                                                                                                           (1 ::
                                                                                                                                              Integer))
                                                                                                                                        (coe
                                                                                                                                           v23)))
                                                                                                                                (coe
                                                                                                                                   (0 ::
                                                                                                                                      Integer))
                                                                                                                                (coe
                                                                                                                                   v4))
                                                                                                                             (coe
                                                                                                                                v21)
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                                   (coe
                                                                                                                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                                      (coe
                                                                                                                                         (\ v22
                                                                                                                                            v23 ->
                                                                                                                                            addInt
                                                                                                                                              (coe
                                                                                                                                                 (1 ::
                                                                                                                                                    Integer))
                                                                                                                                              (coe
                                                                                                                                                 v23)))
                                                                                                                                      (coe
                                                                                                                                         (0 ::
                                                                                                                                            Integer))
                                                                                                                                      (coe
                                                                                                                                         v4))))))))
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                              -> coe
                                                                                                   v16
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError)
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
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                           (coe v0)
                                                                                           (coe
                                                                                              v11))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v13)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
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
                                                                                                       v4))
                                                                                                 (coe
                                                                                                    v14)
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
                                                                                                             v4))))))))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                  -> coe v9
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                          -> case coe v5 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                                                 -> case coe v6 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                                        -> let v9
                                                                 = coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                     (\ v9 ->
                                                                        coe
                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''7495''8658''8804'_2854
                                                                          (coe
                                                                             addInt
                                                                             (coe (1 :: Integer))
                                                                             (coe
                                                                                MAlonzo.Code.Data.List.Base.du_length_268
                                                                                v8)))
                                                                     (coe
                                                                        MAlonzo.Code.Data.Nat.Properties.du_'8804''8658''8804''7495'_2866)
                                                                     (coe
                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.d_T'63'_72
                                                                        (coe
                                                                           MAlonzo.Code.Data.Nat.Base.d__'8804''7495'__14
                                                                           (coe
                                                                              addInt
                                                                              (coe (1 :: Integer))
                                                                              (coe
                                                                                 MAlonzo.Code.Data.List.Base.du_length_268
                                                                                 v8))
                                                                           (coe
                                                                              MAlonzo.Code.Data.List.Base.du_length_268
                                                                              v4))) in
                                                           coe
                                                             (case coe v9 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                                  -> if coe v10
                                                                       then case coe v11 of
                                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22 v12
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                           (coe v0)
                                                                                           (coe v7))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v8)
                                                                                           (coe
                                                                                              MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                    (coe
                                                                                                       (\ v13
                                                                                                          v14 ->
                                                                                                          addInt
                                                                                                            (coe
                                                                                                               (1 ::
                                                                                                                  Integer))
                                                                                                            (coe
                                                                                                               v14)))
                                                                                                    (coe
                                                                                                       (0 ::
                                                                                                          Integer))
                                                                                                    (coe
                                                                                                       v4))
                                                                                                 (coe
                                                                                                    v12)
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                    (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                          (coe
                                                                                                             (\ v13
                                                                                                                v14 ->
                                                                                                                addInt
                                                                                                                  (coe
                                                                                                                     (1 ::
                                                                                                                        Integer))
                                                                                                                  (coe
                                                                                                                     v14)))
                                                                                                          (coe
                                                                                                             (0 ::
                                                                                                                Integer))
                                                                                                          (coe
                                                                                                             v4))))))))
                                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                                       else (let v12
                                                                                   = seq
                                                                                       (coe v11)
                                                                                       (coe v5) in
                                                                             coe
                                                                               (case coe v12 of
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                                                    -> case coe
                                                                                              v13 of
                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                                           -> case coe
                                                                                                     v15 of
                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                                                  -> coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34
                                                                                                             (coe
                                                                                                                v0)
                                                                                                             (coe
                                                                                                                v14))
                                                                                                          (coe
                                                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                             (coe
                                                                                                                v16)
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                                (coe
                                                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                      (coe
                                                                                                                         (\ v18
                                                                                                                            v19 ->
                                                                                                                            addInt
                                                                                                                              (coe
                                                                                                                                 (1 ::
                                                                                                                                    Integer))
                                                                                                                              (coe
                                                                                                                                 v19)))
                                                                                                                      (coe
                                                                                                                         (0 ::
                                                                                                                            Integer))
                                                                                                                      (coe
                                                                                                                         v4))
                                                                                                                   (coe
                                                                                                                      v17)
                                                                                                                   (coe
                                                                                                                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                      (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                            (coe
                                                                                                                               (\ v18
                                                                                                                                  v19 ->
                                                                                                                                  addInt
                                                                                                                                    (coe
                                                                                                                                       (1 ::
                                                                                                                                          Integer))
                                                                                                                                    (coe
                                                                                                                                       v19)))
                                                                                                                            (coe
                                                                                                                               (0 ::
                                                                                                                                  Integer))
                                                                                                                            (coe
                                                                                                                               v4))))))))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                    -> coe v12
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                                                                _ -> MAlonzo.RTE.mazUnreachableError)
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> case coe v5 of
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
                                                                                             (\ v11
                                                                                                v12 ->
                                                                                                addInt
                                                                                                  (coe
                                                                                                     (1 ::
                                                                                                        Integer))
                                                                                                  (coe
                                                                                                     v12)))
                                                                                          (coe
                                                                                             (0 ::
                                                                                                Integer))
                                                                                          (coe v4))
                                                                                       (coe v10)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                          (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                (coe
                                                                                                   (\ v11
                                                                                                      v12 ->
                                                                                                      addInt
                                                                                                        (coe
                                                                                                           (1 ::
                                                                                                              Integer))
                                                                                                        (coe
                                                                                                           v12)))
                                                                                                (coe
                                                                                                   (0 ::
                                                                                                      Integer))
                                                                                                (coe
                                                                                                   v4))))))))
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                        -> coe v5
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError
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
