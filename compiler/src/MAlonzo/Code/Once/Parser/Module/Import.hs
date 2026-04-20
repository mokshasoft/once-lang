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

module MAlonzo.Code.Once.Parser.Module.Import where

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
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Induction.WellFounded
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Module.Import.parseModulePath-WFB
d_parseModulePath'45'WFB_10 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  MAlonzo.Code.Induction.WellFounded.T_Acc_42 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseModulePath'45'WFB_10 v0 ~v1
  = du_parseModulePath'45'WFB_10 v0
du_parseModulePath'45'WFB_10 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_parseModulePath'45'WFB_10 v0
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
                                  = coe
                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                         (coe v4)) in
                            coe
                              (case coe v5 of
                                 (:) v8 v9
                                   -> case coe v8 of
                                        MAlonzo.Code.Once.Parser.Token.C_TDot_44
                                          -> let v10 = coe du_parseModulePath'45'WFB_10 (coe v9) in
                                             coe
                                               (case coe v10 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                    -> case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                             (coe v3) (coe v12))
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14)
                                                                             (coe
                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                (coe
                                                                                   MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                   (coe
                                                                                      (\ v16 v17 ->
                                                                                         addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v17)))
                                                                                   (coe
                                                                                      (0 ::
                                                                                         Integer))
                                                                                   (coe v9))
                                                                                (coe v15)
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                   (coe
                                                                                      addInt
                                                                                      (coe
                                                                                         (1 ::
                                                                                            Integer))
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
                                                                                         (coe v9)))
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                      (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
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
                                                                                               v9))))
                                                                                   (coe v6)))))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                               (coe v3)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))
                                                            (coe v4))
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        _ -> coe v7
                                 _ -> coe v7)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.Import.parseModulePathB
d_parseModulePathB_76 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseModulePathB_76 v0
  = coe du_parseModulePath'45'WFB_10 (coe v0)
-- Once.Parser.Module.Import.parseModulePath
d_parseModulePath_80 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseModulePath_80 v0
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
                                     MAlonzo.Code.Once.Parser.Token.C_TDot_44
                                       -> let v9 = coe du_parseModulePath'45'WFB_10 (coe v8) in
                                          coe
                                            (case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                               -> let v15
                                                                        = coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
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
                                                 -> let v10
                                                          = coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe v3)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                    coe
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe v10) (coe v5)))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> let v9
                                                = coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                          coe
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v9) (coe v5)))
                              _ -> let v7
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                   coe
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                                           (coe v5)))
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
-- Once.Parser.Module.Import.parseImportAliasB
d_parseImportAliasB_98 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseImportAliasB_98 v0 v1
  = let v2
          = coe
              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe
                    MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42
                    (coe
                       MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_30 (coe v0)
                       (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                    (coe
                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                       (coe MAlonzo.Code.Data.List.Base.du_length_268 v1)))) in
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
                                  (coe ("as" :: Data.Text.Text))) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (let v9
                                               = MAlonzo.Code.Once.Parser.Module.Core.d_anyWordB_118
                                                   (coe v4) in
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
                                                                         MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42
                                                                         (coe
                                                                            MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_30
                                                                            (coe v0)
                                                                            (coe
                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                               (coe v11))))
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
                                                                                     (\ v15 v16 ->
                                                                                        addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe
                                                                                             v16)))
                                                                                  (coe
                                                                                     (0 :: Integer))
                                                                                  (coe v4))
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
                                                                                           v4))))))))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Once.Parser.Module.Core.C_DImport_42
                                                 (coe
                                                    MAlonzo.Code.Once.Parser.Module.Core.C_mkImport_30
                                                    (coe v0)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe v1)
                                                 (coe
                                                    MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                                    (coe
                                                       MAlonzo.Code.Data.List.Base.du_foldr_216
                                                       (coe
                                                          (\ v9 v10 ->
                                                             addInt (coe (1 :: Integer)) (coe v10)))
                                                       (coe (0 :: Integer)) (coe v1))))))
                          _ -> MAlonzo.RTE.mazUnreachableError)
                _ -> coe v2
         _ -> coe v2)
-- Once.Parser.Module.Import.parseImportAlias
d_parseImportAlias_148 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseImportAlias_148 v0 v1
  = let v2 = d_parseImportAliasB_98 (coe v0) (coe v1) in
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
-- Once.Parser.Module.Import.parseImportB
d_parseImportB_172 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseImportB_172 v0
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
                                     MAlonzo.Code.Once.Parser.Token.C_TDot_44
                                       -> let v9 = coe du_parseModulePath'45'WFB_10 (coe v8) in
                                          coe
                                            (case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                               -> let v15
                                                                        = coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                            (coe v3) (coe v11) in
                                                                  coe
                                                                    (let v16
                                                                           = coe
                                                                               MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                               (coe
                                                                                  MAlonzo.Code.Data.List.Base.du_foldr_216
                                                                                  (coe
                                                                                     (\ v16 v17 ->
                                                                                        addInt
                                                                                          (coe
                                                                                             (1 ::
                                                                                                Integer))
                                                                                          (coe
                                                                                             v17)))
                                                                                  (coe
                                                                                     (0 :: Integer))
                                                                                  (coe v8))
                                                                               (coe v14)
                                                                               (coe
                                                                                  MAlonzo.Code.Data.Nat.Properties.du_'60''45'trans_3122
                                                                                  (coe
                                                                                     addInt
                                                                                     (coe
                                                                                        (1 ::
                                                                                           Integer))
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
                                                                                        (coe v8)))
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                                                                     (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
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
                                                                                              v8))))
                                                                                  (coe v6)) in
                                                                     coe
                                                                       (let v17
                                                                              = d_parseImportAliasB_98
                                                                                  (coe v15)
                                                                                  (coe v13) in
                                                                        coe
                                                                          (case coe v17 of
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v18
                                                                               -> case coe v18 of
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
                                                                                                           MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                                           (coe
                                                                                                              v22)
                                                                                                           (coe
                                                                                                              v16))))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                               -> coe v17
                                                                             _ -> MAlonzo.RTE.mazUnreachableError)))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> let v10
                                                          = coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe v3)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                    coe
                                                      (let v11
                                                             = d_parseImportAliasB_98
                                                                 (coe v10) (coe v5) in
                                                       coe
                                                         (case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                              -> case coe v12 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe v13)
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v15)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                          (coe v16)
                                                                                          (coe
                                                                                             v6))))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> coe v11
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> let v9
                                                = coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                          coe
                                            (let v10 = d_parseImportAliasB_98 (coe v9) (coe v5) in
                                             coe
                                               (case coe v10 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                    -> case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v12)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe v14)
                                                                             (coe
                                                                                MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                                (coe v15)
                                                                                (coe v6))))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v10
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> let v7
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                   coe
                                     (let v8 = d_parseImportAliasB_98 (coe v7) (coe v5) in
                                      coe
                                        (case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                             -> case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                    -> case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v10)
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v12)
                                                                      (coe
                                                                         MAlonzo.Code.Data.Nat.Properties.du_'8804''45''60''45'trans_3128
                                                                         (coe v13) (coe v6))))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v8
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> let v7 = d_parseImportAliasB_98 (coe v3) (coe v5) in
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
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Module.Import.parseImport
d_parseImport_216 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseImport_216 v0
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
                                     MAlonzo.Code.Once.Parser.Token.C_TDot_44
                                       -> let v9 = coe du_parseModulePath'45'WFB_10 (coe v8) in
                                          coe
                                            (case coe v9 of
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                                 -> case coe v10 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                        -> case coe v12 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                               -> let v15
                                                                        = coe
                                                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                            (coe v3) (coe v11) in
                                                                  coe
                                                                    (let v16
                                                                           = d_parseImportAliasB_98
                                                                               (coe v15)
                                                                               (coe v13) in
                                                                     coe
                                                                       (case coe v16 of
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                                                            -> case coe v17 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                                                   -> case coe
                                                                                             v19 of
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                               (coe
                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                  (coe
                                                                                                     v18)
                                                                                                  (coe
                                                                                                     v20))
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                            -> case coe v16 of
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
                                                                                                            v18)
                                                                                                         (coe
                                                                                                            v20))
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                                   -> coe v16
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError))
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                 -> let v10
                                                          = coe
                                                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                              (coe v3)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                    coe
                                                      (let v11
                                                             = d_parseImportAliasB_98
                                                                 (coe v10) (coe v5) in
                                                       coe
                                                         (case coe v11 of
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                              -> case coe v12 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                     -> case coe v14 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                            -> coe
                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe v13)
                                                                                    (coe v15))
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                              -> case coe v11 of
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                                     -> case coe v12 of
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                                            -> case coe v14 of
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                                                                   -> coe
                                                                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v13)
                                                                                           (coe
                                                                                              v15))
                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                     -> coe v11
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                               _ -> MAlonzo.RTE.mazUnreachableError)
                                     _ -> let v9
                                                = coe
                                                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                          coe
                                            (let v10 = d_parseImportAliasB_98 (coe v9) (coe v5) in
                                             coe
                                               (case coe v10 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                    -> case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> case coe v13 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v12) (coe v14))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> case coe v10 of
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v11
                                                           -> case coe v11 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                  -> case coe v13 of
                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                         -> coe
                                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe v12)
                                                                                 (coe v14))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                           -> coe v10
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError))
                              _ -> let v7
                                         = coe
                                             MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v3)
                                             (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                   coe
                                     (let v8 = d_parseImportAliasB_98 (coe v7) (coe v5) in
                                      coe
                                        (case coe v8 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                             -> case coe v9 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                    -> case coe v11 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                           -> coe
                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v10) (coe v12))
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                             -> case coe v8 of
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                                    -> case coe v9 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                           -> case coe v11 of
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                                                                  -> coe
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v10) (coe v12))
                                                                _ -> MAlonzo.RTE.mazUnreachableError
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                    -> coe v8
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> case coe v1 of
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
                         -> case coe v4 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                                -> let v7 = d_parseImportAliasB_98 (coe v3) (coe v5) in
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
                                       -> coe
                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                               (coe v5))
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
