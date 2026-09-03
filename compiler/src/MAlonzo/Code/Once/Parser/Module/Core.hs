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

module MAlonzo.Code.Once.Parser.Module.Core where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Expr
import qualified MAlonzo.Code.Once.Parser.ExprRelation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.SigEffect
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.Parser.Module.Core.AllocStrategy
d_AllocStrategy_8 = ()
data T_AllocStrategy_8
  = C_Stack_10 | C_Heap_12 | C_Pool_14 | C_Arena_16 | C_Const_18
-- Once.Parser.Module.Core.Import
d_Import_20 = ()
data T_Import_20
  = C_mkImport_30 [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                  (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
-- Once.Parser.Module.Core.Import.path
d_path_26 ::
  T_Import_20 -> [MAlonzo.Code.Agda.Builtin.String.T_String_6]
d_path_26 v0
  = case coe v0 of
      C_mkImport_30 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.Import.alias
d_alias_28 ::
  T_Import_20 -> Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6
d_alias_28 v0
  = case coe v0 of
      C_mkImport_30 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.Decl
d_Decl_32 = ()
data T_Decl_32
  = C_DTypeSig_34 MAlonzo.Code.Agda.Builtin.String.T_String_6
                  MAlonzo.Code.Once.Type.T_PolyType_240 |
    C_DFunDef_36 MAlonzo.Code.Agda.Builtin.String.T_String_6
                 (Maybe T_AllocStrategy_8)
                 MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 |
    C_DSignature_38 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    (Maybe MAlonzo.Code.Agda.Builtin.String.T_String_6)
                    MAlonzo.Code.Once.Type.T_PolyType_240
                    (Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4) |
    C_DTypeAlias_40 MAlonzo.Code.Agda.Builtin.String.T_String_6
                    [MAlonzo.Code.Agda.Builtin.String.T_String_6]
                    MAlonzo.Code.Once.Type.T_Type_108 |
    C_DImport_42 T_Import_20
-- Once.Parser.Module.Core.Module
d_Module_44 = ()
newtype T_Module_44 = C_mkModule_50 [T_Decl_32]
-- Once.Parser.Module.Core.Module.decls
d_decls_48 :: T_Module_44 -> [T_Decl_32]
d_decls_48 v0
  = case coe v0 of
      C_mkModule_50 v1 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.ParseAtB
d_ParseAtB_54 ::
  () -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseAtB_54 = erased
-- Once.Parser.Module.Core.ParseAtB≤
d_ParseAtB'8804'_66 ::
  () -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseAtB'8804'_66 = erased
-- Once.Parser.Module.Core.parseTypeB-adapt
d_parseTypeB'45'adapt_82 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeB'45'adapt_82 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Parser.TypeRelation.d_ParsesType'45'shrinks_432
                                    (coe v0) (coe v3) (coe v5) (coe v6))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.parseTypeB
d_parseTypeB_92 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeB_92 v0
  = coe
      d_parseTypeB'45'adapt_82 (coe v0)
      (coe MAlonzo.Code.Once.Parser.Type.du_parseTypeWF_134 (coe v0))
-- Once.Parser.Module.Core.parseExprB-adapt
d_parseExprB'45'adapt_102 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseExprB'45'adapt_102 v0 v1
  = case coe v1 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v3 v4
               -> case coe v4 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5)
                                 (coe
                                    MAlonzo.Code.Once.Parser.ExprRelation.du_ParsesExpr'45'shrinks_1162
                                    (coe v0) (coe v6))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.parseExprB
d_parseExprB_112 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseExprB_112 v0
  = coe
      d_parseExprB'45'adapt_102 (coe v0)
      (coe MAlonzo.Code.Once.Parser.Expr.du_parseExprWF_468 (coe v0))
-- Once.Parser.Module.Core.anyWordB
d_anyWordB_118 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_anyWordB_118 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         (:) v2 v3
           -> case coe v2 of
                MAlonzo.Code.Once.Parser.Token.C_TWord_8 v4
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                          (coe
                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                             (coe
                                MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                   (coe
                                      MAlonzo.Code.Data.List.Base.du_foldr_216
                                      (let v5 = \ v5 -> addInt (coe (1 :: Integer)) (coe v5) in
                                       coe (coe (\ v6 -> v5)))
                                      (coe (0 :: Integer)) (coe v3))))))
                _ -> coe v1
         _ -> coe v1)
-- Once.Parser.Module.Core.wordHead
d_wordHead_124 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_wordHead_124 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_is'45'just_20
      (coe d_anyWordB_118 (coe v0))
