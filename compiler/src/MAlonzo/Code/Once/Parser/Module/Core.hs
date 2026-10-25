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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Maybe.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Once.Parser.Expr
import qualified MAlonzo.Code.Once.Parser.ExprRelation
import qualified MAlonzo.Code.Once.Parser.Token
import qualified MAlonzo.Code.Once.Parser.Type
import qualified MAlonzo.Code.Once.Parser.TypeRelation
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax

-- Once.Parser.Module.Core.Resolved
d_Resolved_8 = ()
data T_Resolved_8
  = C_resolved_18 MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122
                  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.Parser.Module.Core.Resolved.rmodule
d_rmodule_14 ::
  T_Resolved_8 -> MAlonzo.Code.Once.Spec.Surface.Syntax.T_Module_122
d_rmodule_14 v0
  = case coe v0 of
      C_resolved_18 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.Resolved.imported
d_imported_16 ::
  T_Resolved_8 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imported_16 v0
  = case coe v0 of
      C_resolved_18 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.ParseAtB
d_ParseAtB_22 ::
  () -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseAtB_22 = erased
-- Once.Parser.Module.Core.ParseAtB≤
d_ParseAtB'8804'_34 ::
  () -> [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> ()
d_ParseAtB'8804'_34 = erased
-- Once.Parser.Module.Core.parseTypeB-adapt
d_parseTypeB'45'adapt_50 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeB'45'adapt_50 v0 v1
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
                                    MAlonzo.Code.Once.Parser.TypeRelation.d_ParsesType'45'shrinks_444
                                    (coe v0) (coe v3) (coe v5) (coe v6))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.parseTypeB
d_parseTypeB_60 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseTypeB_60 v0
  = coe
      d_parseTypeB'45'adapt_50 (coe v0)
      (coe MAlonzo.Code.Once.Parser.Type.du_parseTypeWF_138 (coe v0))
-- Once.Parser.Module.Core.parseExprB-adapt
d_parseExprB'45'adapt_70 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseExprB'45'adapt_70 v0 v1
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
                                    MAlonzo.Code.Once.Parser.ExprRelation.du_ParsesExpr'45'shrinks_1152
                                    (coe v0) (coe v6))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Module.Core.parseExprB
d_parseExprB_80 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_parseExprB_80 v0
  = coe
      d_parseExprB'45'adapt_70 (coe v0)
      (coe MAlonzo.Code.Once.Parser.Expr.du_parseExprWF_468 (coe v0))
-- Once.Parser.Module.Core.anyWordB
d_anyWordB_86 ::
  [MAlonzo.Code.Once.Parser.Token.T_Token_6] ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_anyWordB_86 v0
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
d_wordHead_92 :: [MAlonzo.Code.Once.Parser.Token.T_Token_6] -> Bool
d_wordHead_92 v0
  = coe
      MAlonzo.Code.Data.Maybe.Base.du_is'45'just_20
      (coe d_anyWordB_86 (coe v0))
