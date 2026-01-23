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

module MAlonzo.Code.Once.Parser where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Inline
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.TypeAlias
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.parse
d_parse_4 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Parser.Module.T_Module_42
d_parse_4 v0
  = let v1
          = MAlonzo.Code.Once.Parser.Core.d_expect_162
              (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_64) in
    coe
      (let v2
             = MAlonzo.Code.Once.Parser.Lexer.d_tokenize_202
                 (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0) in
       coe
         (let v3
                = MAlonzo.Code.Once.Parser.Core.d_expect_162
                    (coe MAlonzo.Code.Once.Parser.Token.C_TNewline_64)
                    (coe
                       MAlonzo.Code.Once.Parser.Lexer.d_tokenize_202
                       (coe MAlonzo.Code.Agda.Builtin.String.d_primStringToList_12 v0)) in
          coe
            (case coe v3 of
               MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
                 -> case coe v4 of
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                        -> let v7
                                 = coe
                                     MAlonzo.Code.Once.Parser.Core.du_many_280 (coe v1) (coe v6) in
                           coe
                             (case coe v7 of
                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                  -> case coe v8 of
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                         -> let v11
                                                  = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240
                                                      (coe v10) in
                                            coe
                                              (case coe v11 of
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                                   -> case coe v12 of
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                          -> let v15
                                                                   = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                                                       (coe v13) (coe v14) in
                                                             coe
                                                               (case coe v15 of
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                    -> case coe v16 of
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                                                           -> let v19
                                                                                    = coe
                                                                                        MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                        (coe v17) in
                                                                              coe
                                                                                (coe
                                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                   (coe v19))
                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                    -> let v16
                                                                             = coe
                                                                                 MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                                       coe
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                            (coe v16))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                   -> let v12
                                                            = coe
                                                                MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                                                      coe
                                                        (let v13
                                                               = coe
                                                                   MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                   (coe v12) in
                                                         coe
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                              (coe v13)))
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError
                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                  -> let v8
                                           = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240
                                               (coe v6) in
                                     coe
                                       (case coe v8 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                            -> case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                   -> let v12
                                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                                                (coe v10) (coe v11) in
                                                      coe
                                                        (case coe v12 of
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                             -> case coe v13 of
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                    -> let v16
                                                                             = coe
                                                                                 MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                                 (coe v14) in
                                                                       coe
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                            (coe v16))
                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                             -> let v13
                                                                      = coe
                                                                          MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                                                coe
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                     (coe v13))
                                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> let v9
                                                     = coe
                                                         MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                                               coe
                                                 (let v10
                                                        = coe
                                                            MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                            (coe v9) in
                                                  coe
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                       (coe v10)))
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError)
                      _ -> MAlonzo.RTE.mazUnreachableError
               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                 -> let v4
                          = MAlonzo.Code.Once.Parser.Module.d_parseDecl_240 (coe v2) in
                    coe
                      (case coe v4 of
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                           -> case coe v5 of
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                                  -> let v8
                                           = MAlonzo.Code.Once.Parser.Module.d_parseDeclsAfter_468
                                               (coe v6) (coe v7) in
                                     coe
                                       (case coe v8 of
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                                            -> case coe v9 of
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                                   -> let v12
                                                            = coe
                                                                MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                                (coe v10) in
                                                      coe
                                                        (coe
                                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                           (coe v12))
                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                            -> let v9
                                                     = coe
                                                         MAlonzo.Code.Once.Parser.Module.C_mkModule_48
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) in
                                               coe
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                    (coe v9))
                                          _ -> MAlonzo.RTE.mazUnreachableError)
                                _ -> MAlonzo.RTE.mazUnreachableError
                         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                           -> let v5 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
                              coe
                                (let v6
                                       = coe
                                           MAlonzo.Code.Once.Parser.Module.C_mkModule_48 (coe v5) in
                                 coe (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v6)))
                         _ -> MAlonzo.RTE.mazUnreachableError)
               _ -> MAlonzo.RTE.mazUnreachableError)))
-- Once.Parser.extractAliases
d_extractAliases_18 ::
  MAlonzo.Code.Once.Parser.Module.T_Module_42 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extractAliases_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.C_mkModule_48 v1
        -> coe du_go_26 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.go
d_go_26 ::
  [MAlonzo.Code.Once.Parser.Module.T_Decl_30] ->
  [MAlonzo.Code.Once.Parser.Module.T_Decl_30] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_26 ~v0 v1 = du_go_26 v1
du_go_26 ::
  [MAlonzo.Code.Once.Parser.Module.T_Decl_30] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_26 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = coe du_go_26 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.C_DTypeAlias_38 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v6)))
                       (coe du_go_26 (coe v2))
                _ -> coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo
d_FunInfo_38 = ()
data T_FunInfo_38
  = C_mkFunInfo_56 MAlonzo.Code.Agda.Builtin.String.T_String_6
                   MAlonzo.Code.Once.Type.T_Type_32
                   (Maybe MAlonzo.Code.Once.Parser.Module.T_AllocStrategy_6)
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
-- Once.Parser.FunInfo.funName
d_funName_48 ::
  T_FunInfo_38 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_funName_48 v0
  = case coe v0 of
      C_mkFunInfo_56 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funType
d_funType_50 :: T_FunInfo_38 -> MAlonzo.Code.Once.Type.T_Type_32
d_funType_50 v0
  = case coe v0 of
      C_mkFunInfo_56 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funAlloc
d_funAlloc_52 ::
  T_FunInfo_38 ->
  Maybe MAlonzo.Code.Once.Parser.Module.T_AllocStrategy_6
d_funAlloc_52 v0
  = case coe v0 of
      C_mkFunInfo_56 v1 v2 v3 v4 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funBody
d_funBody_54 ::
  T_FunInfo_38 -> MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_funBody_54 v0
  = case coe v0 of
      C_mkFunInfo_56 v1 v2 v3 v4 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.extractFunctions
d_extractFunctions_58 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Parser.Module.T_Module_42 -> [T_FunInfo_38]
d_extractFunctions_58 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.C_mkModule_48 v2
        -> coe
             du_go_68 (coe v0) (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.go
d_go_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.T_Decl_30] ->
  [MAlonzo.Code.Once.Parser.Module.T_Decl_30] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_FunInfo_38]
d_go_68 v0 ~v1 v2 v3 = du_go_68 v0 v2 v3
du_go_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.T_Decl_30] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_FunInfo_38]
du_go_68 v0 v1 v2
  = case coe v1 of
      [] -> coe v1
      (:) v3 v4
        -> let v5 = coe du_go_68 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Parser.Module.C_DTypeSig_32 v6 v7
                  -> coe
                       du_go_68 (coe v0) (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                             (coe
                                MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_122 (coe v0)
                                (coe v7))))
                MAlonzo.Code.Once.Parser.Module.C_DFunDef_34 v6 v7 v8
                  -> case coe v2 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                         -> case coe v9 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v10 v11
                                -> let v12
                                         = coe
                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                             erased
                                             (\ v12 ->
                                                coe
                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                  (coe v10))
                                             (coe
                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                (coe v10) (coe v6)) in
                                   coe
                                     (case coe v12 of
                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                          -> if coe v13
                                               then coe
                                                      seq (coe v14)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                         (coe
                                                            C_mkFunInfo_56 (coe v6) (coe v11)
                                                            (coe v7) (coe v8))
                                                         (coe
                                                            du_go_68 (coe v0) (coe v4)
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)))
                                               else coe
                                                      seq (coe v14)
                                                      (coe
                                                         du_go_68 (coe v0) (coe v4)
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> coe v5
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.inlineAll
d_inlineAll_120 :: Integer -> [T_FunInfo_38] -> [T_FunInfo_38]
d_inlineAll_120 v0 v1
  = coe
      du_go_130 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
-- Once.Parser._.go
d_go_130 ::
  Integer ->
  [T_FunInfo_38] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_FunInfo_38] -> [T_FunInfo_38]
d_go_130 v0 ~v1 v2 v3 = du_go_130 v0 v2 v3
du_go_130 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_FunInfo_38] -> [T_FunInfo_38]
du_go_130 v0 v1 v2
  = case coe v2 of
      [] -> coe v2
      (:) v3 v4
        -> case coe v3 of
             C_mkFunInfo_56 v5 v6 v7 v8
               -> coe
                    MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                    (coe
                       C_mkFunInfo_56 (coe v5) (coe v6) (coe v7)
                       (coe
                          MAlonzo.Code.Once.Parser.Inline.d_inlineReferences_68 (coe v0)
                          (coe v1) (coe v8)))
                    (coe
                       du_go_130 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v8))
                          (coe v1))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
