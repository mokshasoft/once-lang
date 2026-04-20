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

module MAlonzo.Code.Once.Parser.Module.Alloc where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Module.Alloc.parseAllocB
d_parseAllocB_10 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseAllocB_10 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TAt_40
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
                                                (coe v6) (coe ("stack" :: Data.Text.Text))) in
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
                                                               MAlonzo.Code.Once.Parser.Module.Core.C_Stack_10)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                               (coe v5)
                                                               (coe
                                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                  (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                                     (coe
                                                                        MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                        (coe
                                                                           (\ v10 v11 ->
                                                                              addInt
                                                                                (coe (1 :: Integer))
                                                                                (coe v11)))
                                                                        (coe (0 :: Integer))
                                                                        (coe v5)))))))
                                               else coe
                                                      seq (coe v9)
                                                      (let v10
                                                             = coe
                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                 erased
                                                                 (\ v10 ->
                                                                    coe
                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                      (coe v6))
                                                                 (coe
                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                    (coe v6)
                                                                    (coe
                                                                       ("heap"
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
                                                                                   MAlonzo.Code.Once.Parser.Module.Core.C_Heap_12)
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                   (coe v5)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                      (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
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
                                                                                               v5)))))))
                                                                   else coe
                                                                          seq (coe v12)
                                                                          (let v13
                                                                                 = coe
                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                     erased
                                                                                     (\ v13 ->
                                                                                        coe
                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                          (coe v6))
                                                                                     (coe
                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                        (coe v6)
                                                                                        (coe
                                                                                           ("pool"
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
                                                                                                       MAlonzo.Code.Once.Parser.Module.Core.C_Pool_14)
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       (coe
                                                                                                          v5)
                                                                                                       (coe
                                                                                                          MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                          (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                                                (coe
                                                                                                                   (\ v16
                                                                                                                      v17 ->
                                                                                                                      addInt
                                                                                                                        (coe
                                                                                                                           (1 ::
                                                                                                                              Integer))
                                                                                                                        (coe
                                                                                                                           v17)))
                                                                                                                (coe
                                                                                                                   (0 ::
                                                                                                                      Integer))
                                                                                                                (coe
                                                                                                                   v5)))))))
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
                                                                                                                 v6))
                                                                                                         (coe
                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                            (coe
                                                                                                               v6)
                                                                                                            (coe
                                                                                                               ("arena"
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
                                                                                                                           MAlonzo.Code.Once.Parser.Module.Core.C_Arena_16)
                                                                                                                        (coe
                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                           (coe
                                                                                                                              v5)
                                                                                                                           (coe
                                                                                                                              MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                              (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
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
                                                                                                                                       v5)))))))
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
                                                                                                                                     v6))
                                                                                                                             (coe
                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                (coe
                                                                                                                                   v6)
                                                                                                                                (coe
                                                                                                                                   ("const"
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
                                                                                                                                               MAlonzo.Code.Once.Parser.Module.Core.C_Const_18)
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  v5)
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                                                                                  (MAlonzo.Code.Data.Nat.Properties.d_n'8804'1'43'n_2988
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
                                                                                                                                                           v5)))))))
                                                                                                                               else coe
                                                                                                                                      seq
                                                                                                                                      (coe
                                                                                                                                         v21)
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v1
                       _ -> coe v1
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Module.Alloc.parseAlloc
d_parseAlloc_76 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseAlloc_76 v0
  = let v1 = d_parseAllocB_10 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v5))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.Alloc.tryAllocB
d_tryAllocB_96 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryAllocB_96 v0
  = let v1 = d_parseAllocB_10 (coe v0) in
    coe
      (case coe v1 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                  -> case coe v4 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                              (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3))
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                    (coe v6)))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0)
                   (coe
                      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                      (coe
                         MAlonzo.Code.Data.List.Base.du_foldr_216
                         (coe (\ v2 v3 -> addInt (coe (1 :: Integer)) (coe v3)))
                         (coe (0 :: Integer)) (coe v0))))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.Alloc.tryAlloc
d_tryAlloc_114 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_tryAlloc_114 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe d_tryAllocB_96 (coe v0)))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
         (coe
            MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
            (coe d_tryAllocB_96 (coe v0))))
