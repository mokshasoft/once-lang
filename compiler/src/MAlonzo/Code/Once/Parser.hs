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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Parser.Core
import qualified MAlonzo.Code.Once.Parser.Inline
import qualified MAlonzo.Code.Once.Parser.Lexer
import qualified MAlonzo.Code.Once.Parser.Module
import qualified MAlonzo.Code.Once.Parser.Module.Core
import qualified MAlonzo.Code.Once.Parser.TypeAlias
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.parse
d_parse_4 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_Module_44
d_parse_4 v0
  = let v1
          = coe
              MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                 (let v1
                        = MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v0) in
                  coe
                    (let v2
                           = MAlonzo.Code.Once.Parser.Core.d_skipNewlines_278
                               (coe
                                  MAlonzo.Code.Once.Parser.Lexer.d_tokenizeString_630 (coe v0)) in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
                            -> case coe v3 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                                   -> let v6
                                            = MAlonzo.Code.Once.Parser.Module.d_parseDeclB_8
                                                (coe v5) in
                                      coe
                                        (let v7
                                               = coe
                                                   MAlonzo.Code.Once.Parser.Module.du_skipNewlines'45''8804'_174
                                                   (coe v1) in
                                         coe
                                           (case coe v6 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v8
                                                -> case coe v8 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                                                       -> case coe v10 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                                                              -> let v13
                                                                       = coe
                                                                           MAlonzo.Code.Once.Parser.Module.du_parseDeclsWF_282
                                                                           (coe v11) in
                                                                 coe
                                                                   (case coe v13 of
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                                        -> case coe v15 of
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                                               -> coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                       (coe v9)
                                                                                       (coe v14))
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       (coe v16)
                                                                                       (coe
                                                                                          MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                          (coe v17)
                                                                                          (coe
                                                                                             MAlonzo.Code.Data.Nat.Properties.du_'8804''45'trans_2908
                                                                                             (coe
                                                                                                MAlonzo.Code.Data.Nat.Properties.du_'60''8658''8804'_2998
                                                                                                (coe
                                                                                                   v12))
                                                                                             (coe
                                                                                                v7))))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                      _ -> MAlonzo.RTE.mazUnreachableError)
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                                     (coe
                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                        (coe v5) (coe v7))
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                            -> coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1)
                                    (coe
                                       MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                       (coe
                                          MAlonzo.Code.Data.List.Base.du_foldr_216
                                          (coe (\ v3 v4 -> addInt (coe (1 :: Integer)) (coe v4)))
                                          (coe (0 :: Integer)) (coe v1))))
                          _ -> MAlonzo.RTE.mazUnreachableError)))) in
    coe (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v1))
-- Once.Parser.extractAliases
d_extractAliases_18 ::
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_extractAliases_18 v0
  = case coe v0 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v1
        -> coe du_go_26 (coe v1)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.go
d_go_26 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_go_26 ~v0 v1 = du_go_26 v1
du_go_26 ::
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
du_go_26 v0
  = case coe v0 of
      [] -> coe v0
      (:) v1 v2
        -> let v3 = coe du_go_26 (coe v2) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeAlias_40 v4 v5 v6
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
                   MAlonzo.Code.Once.Type.T_Type_38
                   (Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8)
                   MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
-- Once.Parser.FunInfo.funName
d_funName_48 ::
  T_FunInfo_38 -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_funName_48 v0
  = case coe v0 of
      C_mkFunInfo_56 v1 v2 v3 v4 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funType
d_funType_50 :: T_FunInfo_38 -> MAlonzo.Code.Once.Type.T_Type_38
d_funType_50 v0
  = case coe v0 of
      C_mkFunInfo_56 v1 v2 v3 v4 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.FunInfo.funAlloc
d_funAlloc_52 ::
  T_FunInfo_38 ->
  Maybe MAlonzo.Code.Once.Parser.Module.Core.T_AllocStrategy_8
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
  MAlonzo.Code.Once.Parser.Module.Core.T_Module_44 -> [T_FunInfo_38]
d_extractFunctions_58 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Parser.Module.Core.C_mkModule_50 v2
        -> coe
             du_go_68 (coe v0) (coe v2)
             (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser._.go
d_go_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_FunInfo_38]
d_go_68 v0 ~v1 v2 v3 = du_go_68 v0 v2 v3
du_go_68 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Once.Parser.Module.Core.T_Decl_32] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> [T_FunInfo_38]
du_go_68 v0 v1 v2
  = case coe v1 of
      [] -> coe v1
      (:) v3 v4
        -> let v5 = coe du_go_68 (coe v0) (coe v4) (coe v2) in
           coe
             (case coe v3 of
                MAlonzo.Code.Once.Parser.Module.Core.C_DTypeSig_34 v6 v7
                  -> coe
                       du_go_68 (coe v0) (coe v4)
                       (coe
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                             (coe
                                MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48 (coe v0)
                                (coe v7))))
                MAlonzo.Code.Once.Parser.Module.Core.C_DFunDef_36 v6 v7 v8
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
                MAlonzo.Code.Once.Parser.Module.Core.C_DPrimitive_38 v6 v7 v8
                  -> case coe v7 of
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v9
                         -> coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 C_mkFunInfo_56
                                 (coe
                                    MAlonzo.Code.Data.String.Base.d__'43''43'__20 v9
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                       ("." :: Data.Text.Text) v6))
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48 (coe v0)
                                    (coe v8))
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                    (coe
                                       MAlonzo.Code.Data.String.Base.d__'43''43'__20 v9
                                       (coe
                                          MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                          ("." :: Data.Text.Text) v6))))
                              (coe
                                 du_go_68 (coe v0) (coe v4)
                                 (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18))
                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                         -> coe
                              MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                              (coe
                                 C_mkFunInfo_56 (coe v6)
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeAlias.d_expandAliases_48 (coe v0)
                                    (coe v8))
                                 (coe v7) (coe MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 (coe v6)))
                              (coe du_go_68 (coe v0) (coe v4) (coe v7))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.inlineAll
d_inlineAll_136 :: Integer -> [T_FunInfo_38] -> [T_FunInfo_38]
d_inlineAll_136 v0 v1
  = coe
      du_go_146 (coe v0)
      (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) (coe v1)
-- Once.Parser._.go
d_go_146 ::
  Integer ->
  [T_FunInfo_38] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_FunInfo_38] -> [T_FunInfo_38]
d_go_146 v0 ~v1 v2 v3 = du_go_146 v0 v2 v3
du_go_146 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [T_FunInfo_38] -> [T_FunInfo_38]
du_go_146 v0 v1 v2
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
                       du_go_146 (coe v0)
                       (coe
                          MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                          (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v8))
                          (coe v1))
                       (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
