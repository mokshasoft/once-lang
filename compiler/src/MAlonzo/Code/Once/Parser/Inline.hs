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
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_38 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_38
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4))
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_40 (coe v4)
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v4) (coe v1)) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_42 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_42 (coe v4)
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v4) (coe v1)) (coe v6))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_44 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_44
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4))
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_46 v4 v5 v6 v7 v8
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_46
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4)) (coe v5)
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v5) (coe v1)) (coe v6))
                       (coe v7)
                       (coe
                          d_inlineReferences_68 (coe v0)
                          (coe d_removeDef_38 (coe v7) (coe v1)) (coe v8))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_48 -> coe v2
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_50 v4 -> coe v2
                MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_52 v4 -> coe v2
                MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_54 v4 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_54
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v4)) (coe v5)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_56 v4 v5 v6
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_56 (coe v4)
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                       (coe d_inlineReferences_68 (coe v0) (coe v1) (coe v6))
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_58 v5
                  -> coe
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_58
                       (d_inlineReferences_68 (coe v0) (coe v1) (coe v5))
                _ -> MAlonzo.RTE.mazUnreachableError)
