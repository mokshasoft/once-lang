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

module MAlonzo.Code.Once.Parser.Inline where

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
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.Parser.Inline.Defs
d_Defs_6 :: ()
d_Defs_6 = erased
-- Once.Parser.Inline.lookupDef
d_lookupDef_8 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  Maybe MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_lookupDef_8 v0 v1
  = case coe v1 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe
                                     seq (coe v8)
                                     (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                              else coe seq (coe v8) (coe d_lookupDef_8 (coe v0) (coe v3))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Inline.removeDef
d_removeDef_38 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_removeDef_38 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> let v6
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v6 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe v4)) in
                  coe
                    (case coe v6 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                         -> if coe v7
                              then coe seq (coe v8) (coe d_removeDef_38 (coe v0) (coe v3))
                              else coe
                                     seq (coe v8)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                                        (coe d_removeDef_38 (coe v0) (coe v3)))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Inline.inlineReferences
d_inlineReferences_68 ::
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_inlineReferences_68 v0 v1 v2
  = case coe v0 of
      0 -> coe v2
      _ -> let v3 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
                  -> let v5 = d_lookupDef_8 (coe v4) (coe v1) in
                     coe
                       (case coe v5 of
                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                            -> coe d_inlineReferences_68 (coe v3) (coe v1) (coe v6)
                          MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v2
                          _ -> MAlonzo.RTE.mazUnreachableError)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v4 v5 -> coe v2
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4))
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 (coe v4)
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v4) (coe v1)) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 (coe v4)
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v4) (coe v1)) (coe v6))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4))
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v4 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v5) (coe v1)) (coe v6))
                       (coe v7)
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v7) (coe v1)) (coe v8))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50 -> coe v2
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v4 -> coe v2
                MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v4 -> coe v2
                MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4)) (coe v5)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 (coe v4)
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v6))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60
                       (d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Parser.Inline.pairDesugarVar
d_pairDesugarVar_178 :: MAlonzo.Code.Agda.Builtin.String.T_String_6
d_pairDesugarVar_178 = coe ("$pair_x" :: Data.Text.Text)
-- Once.Parser.Inline.composeDesugarVar
d_composeDesugarVar_180 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_composeDesugarVar_180 = coe ("$compose_x" :: Data.Text.Text)
-- Once.Parser.Inline.curryDesugarVarX
d_curryDesugarVarX_182 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_curryDesugarVarX_182 = coe ("$curry_x" :: Data.Text.Text)
-- Once.Parser.Inline.curryDesugarVarY
d_curryDesugarVarY_184 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_curryDesugarVarY_184 = coe ("$curry_y" :: Data.Text.Text)
-- Once.Parser.Inline.applyDesugarVar
d_applyDesugarVar_186 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6
d_applyDesugarVar_186 = coe ("$apply_p" :: Data.Text.Text)
-- Once.Parser.Inline.expandBuiltins
d_expandBuiltins_188 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_expandBuiltins_188 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1 -> coe v0
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2 -> coe v0
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v1 v2
        -> let v3
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                     (coe d_expandBuiltins_188 (coe v1))
                     (coe d_expandBuiltins_188 (coe v2)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
                  -> case coe v4 of
                       l | (==) l ("apply" :: Data.Text.Text) ->
                           coe
                             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44
                             (coe d_applyDesugarVar_186) (coe d_expandBuiltins_188 (coe v2))
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                      (coe ("fst" :: Data.Text.Text)))
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                      (coe d_applyDesugarVar_186)))
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                      (coe ("snd" :: Data.Text.Text)))
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                      (coe d_applyDesugarVar_186))))
                       l | (==) l ("curry" :: Data.Text.Text) ->
                           coe
                             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42
                             (coe d_curryDesugarVarX_182)
                             (coe
                                MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42
                                (coe d_curryDesugarVarY_184)
                                (coe
                                   MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                   (coe d_expandBuiltins_188 (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                         (coe d_curryDesugarVarX_182))
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                         (coe d_curryDesugarVarY_184)))))
                       _ -> coe v3
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
                  -> case coe v4 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v6
                         -> case coe v6 of
                              l | (==) l ("compose" :: Data.Text.Text) ->
                                  coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42
                                    (coe d_composeDesugarVar_180)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                       (coe d_expandBuiltins_188 (coe v5))
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                          (coe d_expandBuiltins_188 (coe v2))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                             (coe d_composeDesugarVar_180))))
                              l | (==) l ("pair" :: Data.Text.Text) ->
                                  coe
                                    MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42
                                    (coe d_pairDesugarVar_178)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                          (coe d_expandBuiltins_188 (coe v5))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                             (coe d_pairDesugarVar_178)))
                                       (coe
                                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                          (coe d_expandBuiltins_188 (coe v2))
                                          (coe
                                             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36
                                             (coe d_pairDesugarVar_178))))
                              _ -> coe v3
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v6 v7
                         -> case coe v6 of
                              MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v8
                                -> case coe v8 of
                                     l | (==) l ("compose" :: Data.Text.Text) ->
                                         coe
                                           MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                           (coe d_expandBuiltins_188 (coe v7))
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                              (coe d_expandBuiltins_188 (coe v5))
                                              (coe d_expandBuiltins_188 (coe v2)))
                                     l | (==) l ("pair" :: Data.Text.Text) ->
                                         coe
                                           MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                              (coe d_expandBuiltins_188 (coe v7))
                                              (coe d_expandBuiltins_188 (coe v2)))
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
                                              (coe d_expandBuiltins_188 (coe v5))
                                              (coe d_expandBuiltins_188 (coe v2)))
                                     _ -> coe v3
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v1 v2
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 (coe v1)
             (coe d_expandBuiltins_188 (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 (coe v1)
             (coe d_expandBuiltins_188 (coe v2))
             (coe d_expandBuiltins_188 (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v1 v2
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
             (coe d_expandBuiltins_188 (coe v1))
             (coe d_expandBuiltins_188 (coe v2))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v1 v2 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
             (coe d_expandBuiltins_188 (coe v1)) (coe v2)
             (coe d_expandBuiltins_188 (coe v3)) (coe v4)
             (coe d_expandBuiltins_188 (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50 -> coe v0
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v1 -> coe v0
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v1 -> coe v0
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v1 v2
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56
             (coe d_expandBuiltins_188 (coe v1)) (coe v2)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v1 v2 v3
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 (coe v1)
             (coe d_expandBuiltins_188 (coe v2))
             (coe d_expandBuiltins_188 (coe v3))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v2
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60
             (d_expandBuiltins_188 (coe v2))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Inline.expandPairs
d_expandPairs_266 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_expandPairs_266 = coe d_expandBuiltins_188
-- Once.Parser.Inline.subst
d_subst_268 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_subst_268 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
        -> let v4
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v4 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v3)) in
           coe
             (case coe v4 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                  -> if coe v5
                       then coe seq (coe v6) (coe v1)
                       else coe seq (coe v6) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4 -> coe v2
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40
             (coe d_subst_268 (coe v0) (coe v1) (coe v3))
             (coe d_subst_268 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v3 v4
        -> let v5
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v5 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v3)) in
           coe
             (case coe v5 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                  -> if coe v6
                       then coe seq (coe v7) (coe v2)
                       else coe
                              seq (coe v7)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 (coe v3)
                                 (coe d_subst_268 (coe v0) (coe v1) (coe v4)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v3 v4 v5
        -> let v6
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v6 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v3)) in
           coe
             (case coe v6 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                  -> if coe v7
                       then coe
                              seq (coe v8)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 (coe v3)
                                 (coe d_subst_268 (coe v0) (coe v1) (coe v4)) (coe v5))
                       else coe
                              seq (coe v8)
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 (coe v3)
                                 (coe d_subst_268 (coe v0) (coe v1) (coe v4))
                                 (coe d_subst_268 (coe v0) (coe v1) (coe v5)))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v3 v4
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
             (coe d_subst_268 (coe v0) (coe v1) (coe v3))
             (coe d_subst_268 (coe v0) (coe v1) (coe v4))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v3 v4 v5 v6 v7
        -> let v8
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v8 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v0))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                        (coe v4)) in
           coe
             (let v9
                    = coe
                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                        erased
                        (\ v9 ->
                           coe
                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                             (coe v0))
                        (coe
                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                           (coe v6)) in
              coe
                (case coe v8 of
                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                     -> if coe v10
                          then coe
                                 seq (coe v11)
                                 (case coe v9 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                      -> if coe v12
                                           then coe
                                                  seq (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v3))
                                                     (coe v4) (coe v5) (coe v6) (coe v7))
                                           else coe
                                                  seq (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v3))
                                                     (coe v4) (coe v5) (coe v6)
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v7)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                          else coe
                                 seq (coe v11)
                                 (case coe v9 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                      -> if coe v12
                                           then coe
                                                  seq (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v3))
                                                     (coe v4)
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v5))
                                                     (coe v6) (coe v7))
                                           else coe
                                                  seq (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v3))
                                                     (coe v4)
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v5))
                                                     (coe v6)
                                                     (coe d_subst_268 (coe v0) (coe v1) (coe v7)))
                                    _ -> MAlonzo.RTE.mazUnreachableError)
                   _ -> MAlonzo.RTE.mazUnreachableError))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50 -> coe v2
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v3 -> coe v2
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v3 -> coe v2
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v3 v4
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56
             (coe d_subst_268 (coe v0) (coe v1) (coe v3)) (coe v4)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v3 v4 v5
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 (coe v3)
             (coe d_subst_268 (coe v0) (coe v1) (coe v4))
             (coe d_subst_268 (coe v0) (coe v1) (coe v5))
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v4
        -> coe
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60
             (d_subst_268 (coe v0) (coe v1) (coe v4))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Parser.Inline.betaReduceApps
d_betaReduceApps_478 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34
d_betaReduceApps_478 v0 v1
  = case coe v0 of
      0 -> coe v1
      _ -> let v2 = subInt (coe v0) (coe (1 :: Integer)) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3 -> coe v1
                MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4 -> coe v1
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
                  -> let v5 = d_betaReduceApps_478 (coe v2) (coe v3) in
                     coe
                       (let v6
                              = coe
                                  MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 (coe v5)
                                  (coe d_betaReduceApps_478 (coe v2) (coe v4)) in
                        coe
                          (case coe v5 of
                             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v7 v8
                               -> coe
                                    d_betaReduceApps_478 (coe v2)
                                    (coe
                                       d_subst_268 (coe v7)
                                       (coe d_betaReduceApps_478 (coe v2) (coe v4)) (coe v8))
                             _ -> coe v6))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v3 v4
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 (coe v3)
                       (coe d_betaReduceApps_478 (coe v2) (coe v4))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 (coe v3)
                       (coe d_betaReduceApps_478 (coe v2) (coe v4))
                       (coe d_betaReduceApps_478 (coe v2) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v3 v4
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46
                       (coe d_betaReduceApps_478 (coe v2) (coe v3))
                       (coe d_betaReduceApps_478 (coe v2) (coe v4))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v3 v4 v5 v6 v7
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48
                       (coe d_betaReduceApps_478 (coe v2) (coe v3)) (coe v4)
                       (coe d_betaReduceApps_478 (coe v2) (coe v5)) (coe v6)
                       (coe d_betaReduceApps_478 (coe v2) (coe v7))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50 -> coe v1
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v3 -> coe v1
                MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v3 -> coe v1
                MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v3 v4
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56
                       (coe d_betaReduceApps_478 (coe v2) (coe v3)) (coe v4)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v3 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 (coe v3)
                       (coe d_betaReduceApps_478 (coe v2) (coe v4))
                       (coe d_betaReduceApps_478 (coe v2) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v4
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60
                       (d_betaReduceApps_478 (coe v2) (coe v4))
                _ -> MAlonzo.RTE.mazUnreachableError)
