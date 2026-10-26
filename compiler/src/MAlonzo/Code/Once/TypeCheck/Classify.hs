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

module MAlonzo.Code.Once.TypeCheck.Classify where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.Context
import qualified MAlonzo.Code.Once.Spec.Context
import qualified MAlonzo.Code.Once.Spec.Grade
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Surface.Syntax
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Scope
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Classify.emptyImports
d_emptyImports_6 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyImports_6 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.emptyPolyCtx
d_emptyPolyCtx_8 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyPolyCtx_8 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.lookupPoly
d_lookupPoly_10 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly_10 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v1)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v5))
                                 else coe seq (coe v8) (coe d_lookupPoly_10 (coe v3) (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly
d_removePoly_46 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_removePoly_46 v0 v1
  = case coe v1 of
      [] -> coe v1
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v0)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe seq (coe v8) (coe v3)
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.List.C__'8759'__22 (coe v2)
                                           (coe d_removePoly_46 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly-decreases
d_removePoly'45'decreases_88 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_removePoly'45'decreases_88 ~v0 v1 v2 ~v3
  = du_removePoly'45'decreases_88 v1 v2
du_removePoly'45'decreases_88 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_removePoly'45'decreases_88 v0 v1
  = case coe v1 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v0)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                           (MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
                                              (coe
                                                 MAlonzo.Code.Data.List.Base.du_foldr_216
                                                 (coe
                                                    (\ v9 v10 ->
                                                       addInt (coe (1 :: Integer)) (coe v10)))
                                                 (coe (0 :: Integer)) (coe v3))))
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           MAlonzo.Code.Data.Nat.Base.C_s'8804's_34
                                           (coe du_removePoly'45'decreases_88 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupPolyPrefix-decreases
d_lookupPolyPrefix'45'decreases_142 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lookupPolyPrefix'45'decreases_142 v0 v1 ~v2 ~v3 v4 ~v5
  = du_lookupPolyPrefix'45'decreases_142 v0 v1 v4
du_lookupPolyPrefix'45'decreases_142 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lookupPolyPrefix'45'decreases_142 v0 v1 v2
  = case coe v1 of
      (:) v3 v4
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    seq (coe v6)
                    (let v7
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v7 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v5))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v5)
                                  (coe v0)) in
                     coe
                       (case coe v7 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                            -> if coe v8
                                 then coe seq (coe v9) (coe du_aux_184 (coe v2))
                                 else coe
                                        seq (coe v9)
                                        (coe
                                           du_lookupPolyPrefix'45'decreases_142 (coe v0) (coe v4)
                                           (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.aux
d_aux_184 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_aux_184 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13
  = du_aux_184 v12
du_aux_184 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_aux_184 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
-- Once.TypeCheck.Classify.lookupPolyPrefix⇒lookupPoly
d_lookupPolyPrefix'8658'lookupPoly_208 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPolyPrefix'8658'lookupPoly_208 = erased
-- Once.TypeCheck.Classify._.aux
d_aux_250 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_aux_250 = erased
-- Once.TypeCheck.Classify.lookupPoly⇒lookupPolyPrefix
d_lookupPoly'8658'lookupPolyPrefix_274 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly'8658'lookupPolyPrefix_274 v0 v1 ~v2 ~v3 ~v4
  = du_lookupPoly'8658'lookupPolyPrefix_274 v0 v1
du_lookupPoly'8658'lookupPolyPrefix_274 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookupPoly'8658'lookupPolyPrefix_274 v0 v1
  = case coe v0 of
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    seq (coe v5)
                    (let v6
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v6 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v4))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                  (coe v1)) in
                     coe
                       (case coe v6 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                            -> if coe v7
                                 then coe seq (coe v8) (coe du_aux_316 (coe v3))
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           du_lookupPoly'8658'lookupPolyPrefix_274 (coe v3)
                                           (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.aux
d_aux_316 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_PolyType_10 ->
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_aux_316 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_aux_316 v5
du_aux_316 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_aux_316 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) erased
-- Once.TypeCheck.Classify.emptyCtx
d_emptyCtx_330 :: MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112
d_emptyCtx_330
  = coe
      MAlonzo.Code.Once.TypeCheck.Scope.C_mkCtx_144 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.du_'8709'_8)
      (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
      (coe d_emptyImports_6) (coe d_emptyPolyCtx_8)
      (coe d_emptyImports_6)
      (\ v0 -> coe MAlonzo.Code.Once.Spec.Type.du_'8709''8342'_142)
-- Once.TypeCheck.Classify.TopCtx
d_TopCtx_332 = ()
data T_TopCtx_332
  = C_topCtx_342 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                 [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Classify.TopCtx.tsig
d_tsig_338 ::
  T_TopCtx_332 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_tsig_338 v0
  = case coe v0 of
      C_topCtx_342 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.TopCtx.tdefs
d_tdefs_340 ::
  T_TopCtx_332 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_tdefs_340 v0
  = case coe v0 of
      C_topCtx_342 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.emptyTopCtx
d_emptyTopCtx_344 :: T_TopCtx_332
d_emptyTopCtx_344
  = coe C_topCtx_342 (coe d_emptyImports_6) (coe d_emptyImports_6)
-- Once.TypeCheck.Classify.ctxWithImportsAndPolys
d_ctxWithImportsAndPolys_346 ::
  T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112
d_ctxWithImportsAndPolys_346 v0 v1
  = coe
      MAlonzo.Code.Once.TypeCheck.Scope.C_mkCtx_144 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.du_'8709'_8)
      (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
      (coe d_tdefs_340 (coe v0)) (coe v1) (coe d_tsig_338 (coe v0))
      (\ v2 -> coe MAlonzo.Code.Once.Spec.Type.du_'8709''8342'_142)
-- Once.TypeCheck.Classify.ctxAt
d_ctxAt_354 ::
  Integer ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112
d_ctxAt_354 ~v0 v1 v2 v3 = du_ctxAt_354 v1 v2 v3
du_ctxAt_354 ::
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  T_TopCtx_332 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112
du_ctxAt_354 v0 v1 v2
  = coe
      MAlonzo.Code.Once.TypeCheck.Scope.C_mkCtx_144 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.du_'8709'_8)
      (coe MAlonzo.Code.Once.Spec.Context.C_'8709'_12)
      (coe d_tdefs_340 (coe v1)) (coe v2) (coe d_tsig_338 (coe v1))
      (coe v0)
-- Once.TypeCheck.Classify.baseKinds
d_baseKinds_364 ::
  Integer ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
  MAlonzo.Code.Once.Spec.Type.T_Kind_70
d_baseKinds_364 v0
  = case coe v0 of
      0 -> coe
             (\ v1 -> coe MAlonzo.Code.Once.Spec.Type.du_'8709''8342'_142)
      _ -> coe (\ v1 -> coe MAlonzo.Code.Once.Spec.Type.C_base_72)
-- Once.TypeCheck.Classify.LookupLocalView
d_LookupLocalView_376 a0 a1 a2 = ()
data T_LookupLocalView_376
  = C_llv'45'found_390 MAlonzo.Code.Once.Spec.Type.T_Ty_8
                       MAlonzo.Code.Once.Spec.Context.T_Usage_34
                       MAlonzo.Code.Once.Context.T_SVar_36 |
    C_llv'45'not'45'found_392
-- Once.TypeCheck.Classify.inspectLookupLocal
d_inspectLookupLocal_400 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupLocalView_376
d_inspectLookupLocal_400 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.TypeCheck.Scope.d_lookupLocal'45'go_170
              (coe v0)
              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_size_130 (coe v1))
              (coe v2)
              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_named_132 (coe v1))
              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_debruijn_134 (coe v1)) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> case coe v6 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                         -> coe C_llv'45'found_390 v5 v7 v8
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_llv'45'not'45'found_392
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.LookupImportView
d_LookupImportView_432 a0 a1 a2 = ()
data T_LookupImportView_432
  = C_liv'45'found_442 MAlonzo.Code.Once.Spec.Type.T_Ty_8 |
    C_liv'45'not'45'found_444
-- Once.TypeCheck.Classify.inspectLookupImport
d_inspectLookupImport_452 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupImportView_432
d_inspectLookupImport_452 ~v0 v1 v2
  = du_inspectLookupImport_452 v1 v2
du_inspectLookupImport_452 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupImportView_432
du_inspectLookupImport_452 v0 v1
  = let v2
          = MAlonzo.Code.Once.TypeCheck.Scope.d_lookupImport_44
              (coe MAlonzo.Code.Once.TypeCheck.Scope.d_imports_136 (coe v0))
              (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_liv'45'found_442 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_liv'45'not'45'found_444
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.findLocalVarUsage
d_findLocalVarUsage_478 ::
  Integer ->
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_478 ~v0 v1 v2 = du_findLocalVarUsage_478 v1 v2
du_findLocalVarUsage_478 ::
  MAlonzo.Code.Once.TypeCheck.Scope.T_NamedCtx_112 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_findLocalVarUsage_478 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Scope.C_mkCtx_144 v2 v3 v4 v5 v6 v7 v8
        -> coe du_go_494 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.go
d_go_494 ::
  Integer ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  (MAlonzo.Code.Data.Fin.Base.T_Fin_10 ->
   MAlonzo.Code.Once.Spec.Type.T_Kind_70) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_494 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9 v10 v11
  = du_go_494 v8 v10 v11
du_go_494 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Scope.T_Binding_8] ->
  MAlonzo.Code.Once.Spec.Context.T_Ctx_8 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_494 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Spec.Context.C_'8709'_12
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Spec.Context.C__'9656'__16 v6 v7
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
                               (coe MAlonzo.Code.Once.TypeCheck.Scope.d_name_18 (coe v3))) in
                  coe
                    (case coe v8 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                         -> if coe v9
                              then coe
                                     seq (coe v10)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                           (coe MAlonzo.Code.Once.Spec.Grade.C_Many_12)))
                              else coe
                                     seq (coe v10)
                                     (let v11 = coe du_go_494 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v11 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v12
                                             -> case coe v12 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                               v13)
                                                            (coe v14))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v11
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_550 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_550 = erased
-- Once.TypeCheck.Classify.view-other⇒classifyAppHead-nothing
d_view'45'other'8658'classifyAppHead'45'nothing_630 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_view'45'other'8658'classifyAppHead'45'nothing_630 = erased
-- Once.TypeCheck.Classify.GenView
d_GenView_640 a0 = ()
data T_GenView_640
  = C_gv'45'id_642 | C_gv'45'fst_644 | C_gv'45'snd_646 |
    C_gv'45'terminal_648 | C_gv'45'initial_650 | C_gv'45'inl_652 |
    C_gv'45'inr_654 | C_gv'45'unit_656 |
    C_gv'45'other_660 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.TypeCheck.Classify.notGen-ns
d_notGen'45'ns_666 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_notGen'45'ns_666 ~v0 ~v1 ~v2 = du_notGen'45'ns_666
du_notGen'45'ns_666 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_notGen'45'ns_666
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 erased
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.TypeCheck.Classify._.f
d_f_680 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_f_680 = erased
-- Once.TypeCheck.Classify.notGen-shape
d_notGen'45'shape_686 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_notGen'45'shape_686 ~v0 v1 = du_notGen'45'shape_686 v1
du_notGen'45'shape_686 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_notGen'45'shape_686 v0
  = coe
      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
      (coe v0 ("id" :: Data.Text.Text))
      (coe
         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
         (coe v0 ("fst" :: Data.Text.Text))
         (coe
            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
            (coe v0 ("snd" :: Data.Text.Text))
            (coe
               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
               (coe v0 ("terminal" :: Data.Text.Text))
               (coe
                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                  (coe v0 ("initial" :: Data.Text.Text))
                  (coe
                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                     (coe v0 ("inl" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                        (coe v0 ("inr" :: Data.Text.Text))
                        (coe
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                           (coe v0 ("unit" :: Data.Text.Text))
                           (coe
                              MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))
-- Once.TypeCheck.Classify.classifyGen
d_classifyGen_692 ::
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 -> T_GenView_640
d_classifyGen_692 v0
  = case coe v0 of
      MAlonzo.Code.Once.Spec.Name.C_canonical_12 v1
        -> case coe v1 of
             [] -> coe C_gv'45'other_660 (coe du_notGen'45'shape_686 erased)
             (:) v2 v3
               -> case coe v3 of
                    [] -> coe C_gv'45'other_660 (coe du_notGen'45'shape_686 erased)
                    (:) v4 v5
                      -> case coe v5 of
                           []
                             -> let v6
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased (coe (\ v6 -> v6))
                                          (coe
                                             MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                             (coe v2)
                                             (coe MAlonzo.Code.Once.Spec.Name.d_generatorNS_18)) in
                                coe
                                  (case coe v6 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                       -> if coe v7
                                            then coe
                                                   seq (coe v8)
                                                   (let v9
                                                          = coe
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                              erased (coe (\ v9 -> v9))
                                                              (coe
                                                                 MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                 (coe v4)
                                                                 (coe ("id" :: Data.Text.Text))) in
                                                    coe
                                                      (case coe v9 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                           -> if coe v10
                                                                then coe
                                                                       seq (coe v11)
                                                                       (coe C_gv'45'id_642)
                                                                else coe
                                                                       seq (coe v11)
                                                                       (let v12
                                                                              = coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                  erased
                                                                                  (coe
                                                                                     (\ v12 -> v12))
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                     (coe v4)
                                                                                     (coe
                                                                                        ("fst"
                                                                                         ::
                                                                                         Data.Text.Text))) in
                                                                        coe
                                                                          (case coe v12 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                               -> if coe v13
                                                                                    then coe
                                                                                           seq
                                                                                           (coe v14)
                                                                                           (coe
                                                                                              C_gv'45'fst_644)
                                                                                    else coe
                                                                                           seq
                                                                                           (coe v14)
                                                                                           (let v15
                                                                                                  = coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                      erased
                                                                                                      (coe
                                                                                                         (\ v15 ->
                                                                                                            v15))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                         (coe
                                                                                                            v4)
                                                                                                         (coe
                                                                                                            ("snd"
                                                                                                             ::
                                                                                                             Data.Text.Text))) in
                                                                                            coe
                                                                                              (case coe
                                                                                                      v15 of
                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v16 v17
                                                                                                   -> if coe
                                                                                                           v16
                                                                                                        then coe
                                                                                                               seq
                                                                                                               (coe
                                                                                                                  v17)
                                                                                                               (coe
                                                                                                                  C_gv'45'snd_646)
                                                                                                        else coe
                                                                                                               seq
                                                                                                               (coe
                                                                                                                  v17)
                                                                                                               (let v18
                                                                                                                      = coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                          erased
                                                                                                                          (coe
                                                                                                                             (\ v18 ->
                                                                                                                                v18))
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                             (coe
                                                                                                                                v4)
                                                                                                                             (coe
                                                                                                                                ("terminal"
                                                                                                                                 ::
                                                                                                                                 Data.Text.Text))) in
                                                                                                                coe
                                                                                                                  (case coe
                                                                                                                          v18 of
                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v19 v20
                                                                                                                       -> if coe
                                                                                                                               v19
                                                                                                                            then coe
                                                                                                                                   seq
                                                                                                                                   (coe
                                                                                                                                      v20)
                                                                                                                                   (coe
                                                                                                                                      C_gv'45'terminal_648)
                                                                                                                            else coe
                                                                                                                                   seq
                                                                                                                                   (coe
                                                                                                                                      v20)
                                                                                                                                   (let v21
                                                                                                                                          = coe
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                              erased
                                                                                                                                              (coe
                                                                                                                                                 (\ v21 ->
                                                                                                                                                    v21))
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                 (coe
                                                                                                                                                    v4)
                                                                                                                                                 (coe
                                                                                                                                                    ("initial"
                                                                                                                                                     ::
                                                                                                                                                     Data.Text.Text))) in
                                                                                                                                    coe
                                                                                                                                      (case coe
                                                                                                                                              v21 of
                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v22 v23
                                                                                                                                           -> if coe
                                                                                                                                                   v22
                                                                                                                                                then coe
                                                                                                                                                       seq
                                                                                                                                                       (coe
                                                                                                                                                          v23)
                                                                                                                                                       (coe
                                                                                                                                                          C_gv'45'initial_650)
                                                                                                                                                else coe
                                                                                                                                                       seq
                                                                                                                                                       (coe
                                                                                                                                                          v23)
                                                                                                                                                       (let v24
                                                                                                                                                              = coe
                                                                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                  erased
                                                                                                                                                                  (coe
                                                                                                                                                                     (\ v24 ->
                                                                                                                                                                        v24))
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                     (coe
                                                                                                                                                                        v4)
                                                                                                                                                                     (coe
                                                                                                                                                                        ("inl"
                                                                                                                                                                         ::
                                                                                                                                                                         Data.Text.Text))) in
                                                                                                                                                        coe
                                                                                                                                                          (case coe
                                                                                                                                                                  v24 of
                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v25 v26
                                                                                                                                                               -> if coe
                                                                                                                                                                       v25
                                                                                                                                                                    then coe
                                                                                                                                                                           seq
                                                                                                                                                                           (coe
                                                                                                                                                                              v26)
                                                                                                                                                                           (coe
                                                                                                                                                                              C_gv'45'inl_652)
                                                                                                                                                                    else coe
                                                                                                                                                                           seq
                                                                                                                                                                           (coe
                                                                                                                                                                              v26)
                                                                                                                                                                           (let v27
                                                                                                                                                                                  = coe
                                                                                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                      erased
                                                                                                                                                                                      (coe
                                                                                                                                                                                         (\ v27 ->
                                                                                                                                                                                            v27))
                                                                                                                                                                                      (coe
                                                                                                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                         (coe
                                                                                                                                                                                            v4)
                                                                                                                                                                                         (coe
                                                                                                                                                                                            ("inr"
                                                                                                                                                                                             ::
                                                                                                                                                                                             Data.Text.Text))) in
                                                                                                                                                                            coe
                                                                                                                                                                              (case coe
                                                                                                                                                                                      v27 of
                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v28 v29
                                                                                                                                                                                   -> if coe
                                                                                                                                                                                           v28
                                                                                                                                                                                        then coe
                                                                                                                                                                                               seq
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  v29)
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  C_gv'45'inr_654)
                                                                                                                                                                                        else coe
                                                                                                                                                                                               seq
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  v29)
                                                                                                                                                                                               (let v30
                                                                                                                                                                                                      = coe
                                                                                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                          erased
                                                                                                                                                                                                          (coe
                                                                                                                                                                                                             (\ v30 ->
                                                                                                                                                                                                                v30))
                                                                                                                                                                                                          (coe
                                                                                                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                v4)
                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                ("unit"
                                                                                                                                                                                                                 ::
                                                                                                                                                                                                                 Data.Text.Text))) in
                                                                                                                                                                                                coe
                                                                                                                                                                                                  (case coe
                                                                                                                                                                                                          v30 of
                                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v31 v32
                                                                                                                                                                                                       -> if coe
                                                                                                                                                                                                               v31
                                                                                                                                                                                                            then coe
                                                                                                                                                                                                                   seq
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      v32)
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      C_gv'45'unit_656)
                                                                                                                                                                                                            else coe
                                                                                                                                                                                                                   seq
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      v32)
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      C_gv'45'other_660
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                         erased
                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                            erased
                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                               erased
                                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                                  erased
                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                                     erased
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                                        erased
                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                                           erased
                                                                                                                                                                                                                                           (coe
                                                                                                                                                                                                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60
                                                                                                                                                                                                                                              erased
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 MAlonzo.Code.Data.List.Relation.Unary.All.C_'91''93'_50))))))))))
                                                                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            else coe
                                                   seq (coe v8)
                                                   (coe C_gv'45'other_660 (coe du_notGen'45'ns_666))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           (:) v6 v7
                             -> coe C_gv'45'other_660 (coe du_notGen'45'shape_686 erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.ViewBundle
d_ViewBundle_952 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 -> ()
d_ViewBundle_952 = erased
-- Once.TypeCheck.Classify.viewBundle
d_viewBundle_960 ::
  MAlonzo.Code.Once.Spec.Surface.Syntax.T_Expr_68 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_960 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.TypeCheck.Scope.d_classifyAppHeadView_350
         (coe v0))
      erased
