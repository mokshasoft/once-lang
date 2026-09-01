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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Nat.Properties
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.SigEffect
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Classify.Imports
d_Imports_6 :: ()
d_Imports_6 = erased
-- Once.TypeCheck.Classify.emptyImports
d_emptyImports_8 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyImports_8 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.SigEffectCtx
d_SigEffectCtx_10 :: ()
d_SigEffectCtx_10 = erased
-- Once.TypeCheck.Classify.emptySigEffects
d_emptySigEffects_12 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptySigEffects_12
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.lookupSigEffect
d_lookupSigEffect_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.SigEffect.T_SigEffect_4
d_lookupSigEffect_14 v0 v1
  = case coe v0 of
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
                              else coe seq (coe v8) (coe d_lookupSigEffect_14 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.PolyCtx
d_PolyCtx_44 :: ()
d_PolyCtx_44 = erased
-- Once.TypeCheck.Classify.emptyPolyCtx
d_emptyPolyCtx_46 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyPolyCtx_46
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.lookupPoly
d_lookupPoly_48 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly_48 v0 v1
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
                                 else coe seq (coe v8) (coe d_lookupPoly_48 (coe v3) (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly
d_removePoly_84 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_removePoly_84 v0 v1
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
                                           (coe d_removePoly_84 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly-decreases
d_removePoly'45'decreases_126 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_removePoly'45'decreases_126 ~v0 v1 v2 ~v3
  = du_removePoly'45'decreases_126 v1 v2
du_removePoly'45'decreases_126 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_removePoly'45'decreases_126 v0 v1
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
                                           (coe du_removePoly'45'decreases_126 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupPolyPrefix
d_lookupPolyPrefix_170 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPolyPrefix_170 v0 v1
  = case coe v0 of
      [] -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      (:) v2 v3
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> case coe v5 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                      -> let v8
                               = coe
                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                   erased
                                   (\ v8 ->
                                      coe
                                        MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                        (coe v4))
                                   (coe
                                      MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v4)
                                      (coe v1)) in
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
                                                  (coe v6)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     (coe v7) (coe v3))))
                                     else coe
                                            seq (coe v10)
                                            (coe d_lookupPolyPrefix_170 (coe v3) (coe v1))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupPolyPrefix-decreases
d_lookupPolyPrefix'45'decreases_216 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lookupPolyPrefix'45'decreases_216 v0 v1 ~v2 ~v3 v4 ~v5
  = du_lookupPolyPrefix'45'decreases_216 v0 v1 v4
du_lookupPolyPrefix'45'decreases_216 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lookupPolyPrefix'45'decreases_216 v0 v1 v2
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
                                 then coe seq (coe v9) (coe du_aux_258 (coe v2))
                                 else coe
                                        seq (coe v9)
                                        (coe
                                           du_lookupPolyPrefix'45'decreases_216 (coe v0) (coe v4)
                                           (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.aux
d_aux_258 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_aux_258 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13
  = du_aux_258 v12
du_aux_258 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_aux_258 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
-- Once.TypeCheck.Classify.lookupPolyPrefix⇒lookupPoly
d_lookupPolyPrefix'8658'lookupPoly_282 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPolyPrefix'8658'lookupPoly_282 = erased
-- Once.TypeCheck.Classify._.aux
d_aux_324 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_240 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_aux_324 = erased
-- Once.TypeCheck.Classify.NamedCtx
d_NamedCtx_338 = ()
data T_NamedCtx_338
  = C_mkCtx_368 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Context.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Classify.NamedCtx.size
d_size_354 :: T_NamedCtx_338 -> Integer
d_size_354 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.named
d_named_356 ::
  T_NamedCtx_338 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_356 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.debruijn
d_debruijn_358 ::
  T_NamedCtx_338 -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6
d_debruijn_358 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.freshCounter
d_freshCounter_360 :: T_NamedCtx_338 -> Integer
d_freshCounter_360 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.imports
d_imports_362 ::
  T_NamedCtx_338 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_362 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.polys
d_polys_364 ::
  T_NamedCtx_338 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_364 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.sigEffects
d_sigEffects_366 ::
  T_NamedCtx_338 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sigEffects_366 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.emptyCtx
d_emptyCtx_370 :: T_NamedCtx_338
d_emptyCtx_370
  = coe
      C_mkCtx_368 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_8) (coe d_emptyPolyCtx_46)
      (coe d_emptySigEffects_12)
-- Once.TypeCheck.Classify.ctxWithImports
d_ctxWithImports_372 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_338
d_ctxWithImports_372 v0
  = coe
      C_mkCtx_368 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe d_emptyPolyCtx_46)
      (coe d_emptySigEffects_12)
-- Once.TypeCheck.Classify.ctxWithImportsAndPolys
d_ctxWithImportsAndPolys_376 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_338
d_ctxWithImportsAndPolys_376 v0 v1
  = coe
      C_mkCtx_368 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe v1) (coe d_emptySigEffects_12)
-- Once.TypeCheck.Classify.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_382 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_338
d_ctxWithImportsAndSelf_382 v0 v1 v2
  = coe
      d_ctxWithImports_372
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Classify.ctxWithImportsAndSelfAndPolys
d_ctxWithImportsAndSelfAndPolys_390 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_338
d_ctxWithImportsAndSelfAndPolys_390 v0 v1 v2 v3 v4
  = coe
      C_mkCtx_368 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
         (coe v0))
      (coe v1) (coe v2)
-- Once.TypeCheck.Classify.extendNamedCtx
d_extendNamedCtx_402 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_338
d_extendNamedCtx_402 v0 v1 v2
  = case coe v0 of
      C_mkCtx_368 v3 v4 v5 v6 v7 v8 v9
        -> coe
             C_mkCtx_368 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7) (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.bumpFresh
d_bumpFresh_422 :: T_NamedCtx_338 -> T_NamedCtx_338
d_bumpFresh_422 v0
  = case coe v0 of
      C_mkCtx_368 v1 v2 v3 v4 v5 v6 v7
        -> coe
             C_mkCtx_368 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5) (coe v6)
             (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.freshTVar
d_freshTVar_438 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_438 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Classify.lookupImport
d_lookupImport_442 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_lookupImport_442 v0 v1
  = case coe v0 of
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
                              else coe seq (coe v8) (coe d_lookupImport_442 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupLocal-go
d_lookupLocal'45'go_484 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'go_484 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Context.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v7 v8 v9
               -> let v10 = subInt (coe v0) (coe (1 :: Integer)) in
                  coe
                    (let v11
                           = coe
                               MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                               erased
                               (\ v11 ->
                                  coe
                                    MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                    (coe v1))
                               (coe
                                  MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                                  (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v4))) in
                     coe
                       (case coe v11 of
                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                            -> if coe v12
                                 then coe
                                        seq (coe v13)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du_lookup_24
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                                    v7 v8 v9)
                                                 (coe MAlonzo.Code.Data.Fin.Base.C_zero_12))
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.d_singleUse_102
                                                    (coe v0)
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                    (coe MAlonzo.Code.Once.Type.C_One_8))
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Context.C_svar_218
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                 else coe
                                        seq (coe v13)
                                        (let v14
                                               = d_lookupLocal'45'go_484
                                                   (coe v10) (coe v1) (coe v5) (coe v7) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                -> case coe v15 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                              -> case coe v19 of
                                                                   MAlonzo.Code.Once.Surface.Context.C_svar_218 v22
                                                                     -> coe
                                                                          MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             (coe
                                                                                MAlonzo.Code.Once.Surface.Context.du_lookup_24
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                                                                   v7 v8 v9)
                                                                                (coe
                                                                                   MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                   v22))
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Surface.Context.d_singleUse_102
                                                                                   (coe v0)
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                      v22)
                                                                                   (coe
                                                                                      MAlonzo.Code.Once.Type.C_One_8))
                                                                                (coe
                                                                                   MAlonzo.Code.Once.Surface.Context.C_svar_218
                                                                                   (coe
                                                                                      MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                                                      v22))))
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v14
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupLocal
d_lookupLocal_572 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_572 v0 v1
  = coe
      d_lookupLocal'45'go_484 (coe d_size_354 (coe v0)) (coe v1)
      (coe d_named_356 (coe v0)) (coe d_debruijn_358 (coe v0))
-- Once.TypeCheck.Classify.LookupLocalView
d_LookupLocalView_582 a0 a1 = ()
data T_LookupLocalView_582
  = C_llv'45'found_594 MAlonzo.Code.Once.Type.T_Type_108
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_SVar_210 |
    C_llv'45'not'45'found_596
-- Once.TypeCheck.Classify.inspectLookupLocal
d_inspectLookupLocal_602 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupLocalView_582
d_inspectLookupLocal_602 v0 v1
  = let v2
          = d_lookupLocal'45'go_484
              (coe d_size_354 (coe v0)) (coe v1) (coe d_named_356 (coe v0))
              (coe d_debruijn_358 (coe v0)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe C_llv'45'found_594 v4 v6 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_llv'45'not'45'found_596
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.LookupImportView
d_LookupImportView_632 a0 a1 = ()
data T_LookupImportView_632
  = C_liv'45'found_640 MAlonzo.Code.Once.Type.T_Type_108 |
    C_liv'45'not'45'found_642
-- Once.TypeCheck.Classify.inspectLookupImport
d_inspectLookupImport_648 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupImportView_632
d_inspectLookupImport_648 v0 v1
  = let v2
          = d_lookupImport_442 (coe d_imports_362 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_liv'45'found_640 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_liv'45'not'45'found_642
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.composeArgB-lookup
d_composeArgB'45'lookup_670 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB'45'lookup_670 v0 v1 v2
  = let v3 = d_lookupPoly_48 (coe d_polys_364 (coe v0)) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       MAlonzo.Code.Once.Type.d_schemaArrowCodomain_856 (coe v5) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v4
                    = d_lookupImport_442 (coe d_imports_362 (coe v0)) (coe v1) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v5 of
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v6 v7 v8
                            -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v8)
                          _ -> coe v3
                   _ -> coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.composeArgB-fst
d_composeArgB'45'fst_714 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB'45'fst_714 v0 v1
  = let v2
          = d_composeArgB'45'lookup_670
              (coe v0) (coe ("fst" :: Data.Text.Text)) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
         _ -> coe v2)
-- Once.TypeCheck.Classify.composeArgB-snd
d_composeArgB'45'snd_724 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB'45'snd_724 v0 v1
  = let v2
          = d_composeArgB'45'lookup_670
              (coe v0) (coe ("snd" :: Data.Text.Text)) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C__'42'__122 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
         _ -> coe v2)
-- Once.TypeCheck.Classify.composeArgB-rvar
d_composeArgB'45'rvar_734 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB'45'rvar_734 v0 v1 v2
  = let v3
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v3 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v1))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                 (coe ("fst" :: Data.Text.Text))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v4 v5
           -> if coe v4
                then coe
                       seq (coe v5) (coe d_composeArgB'45'fst_714 (coe v0) (coe v2))
                else coe
                       seq (coe v5)
                       (let v6
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v6 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v1))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                                     (coe ("snd" :: Data.Text.Text))) in
                        coe
                          (case coe v6 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                               -> if coe v7
                                    then coe
                                           seq (coe v8)
                                           (coe d_composeArgB'45'snd_724 (coe v0) (coe v2))
                                    else coe
                                           seq (coe v8)
                                           (let v9
                                                  = coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                      erased
                                                      (\ v9 ->
                                                         coe
                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                           (coe v1))
                                                      (coe
                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                         (coe v1) (coe ("id" :: Data.Text.Text))) in
                                            coe
                                              (case coe v9 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                   -> if coe v10
                                                        then coe
                                                               seq (coe v11)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                  (coe v2))
                                                        else coe
                                                               seq (coe v11)
                                                               (let v12
                                                                      = coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                          erased
                                                                          (\ v12 ->
                                                                             coe
                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                               (coe v1))
                                                                          (coe
                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                             (coe v1)
                                                                             (coe
                                                                                ("terminal"
                                                                                 ::
                                                                                 Data.Text.Text))) in
                                                                coe
                                                                  (case coe v12 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                       -> if coe v13
                                                                            then coe
                                                                                   seq (coe v14)
                                                                                   (coe
                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                      (coe
                                                                                         MAlonzo.Code.Once.Type.C_Unit_118))
                                                                            else coe
                                                                                   seq (coe v14)
                                                                                   (coe
                                                                                      d_composeArgB'45'lookup_670
                                                                                      (coe v0)
                                                                                      (coe v1)
                                                                                      (coe v2))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.composeArgB
d_composeArgB_806 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB_806 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> coe d_composeArgB'45'rvar_734 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4
           -> coe
                d_composeArgB'45'lookup_670 (coe v0)
                (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v4))
                (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v8
                         -> let v9
                                  = coe
                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                      erased
                                      (\ v9 ->
                                         coe
                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                           (coe v8))
                                      (coe
                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                         (coe v8) (coe ("compose" :: Data.Text.Text))) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                   -> if coe v10
                                        then coe
                                               seq (coe v11)
                                               (let v12
                                                      = d_composeArgB_806
                                                          (coe v0) (coe v5) (coe v2) in
                                                coe
                                                  (case coe v12 of
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                                       -> coe
                                                            d_composeArgB_806 (coe v0) (coe v7)
                                                            (coe v13)
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                       -> coe v12
                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                        else coe
                                               seq (coe v11)
                                               (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.Type.C_Int_132)
         _ -> coe v3)
-- Once.TypeCheck.Classify.domainOfHead-arrow
d_domainOfHead'45'arrow_912 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_domainOfHead'45'arrow_912 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v3 v4 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.Classify.domainOfHead
d_domainOfHead_916 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_domainOfHead_916 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
           -> coe
                d_domainOfHead'45'arrow_912
                (coe d_lookupImport_442 (coe d_imports_362 (coe v0)) (coe v3))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v3
           -> coe
                d_domainOfHead'45'arrow_912
                (coe
                   d_lookupImport_442 (coe d_imports_362 (coe v0))
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v3)))
         _ -> coe v2)
-- Once.TypeCheck.Classify.composeMid-pick
d_composeMid'45'pick_926 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeMid'45'pick_926 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.composeMid
d_composeMid_932 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeMid_932 v0 v1 v2 v3
  = coe
      d_composeMid'45'pick_926
      (coe d_composeArgB_806 (coe v0) (coe v2) (coe v3))
      (coe d_domainOfHead_916 (coe v0) (coe v1))
-- Once.TypeCheck.Classify.findLocalVarUsage
d_findLocalVarUsage_944 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_944 v0 v1
  = case coe v0 of
      C_mkCtx_368 v2 v3 v4 v5 v6 v7 v8
        -> coe du_go_960 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.go
d_go_960 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_960 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10
  = du_go_960 v7 v9 v10
du_go_960 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_960 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.Context.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v6 v7 v8
               -> let v9
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v9 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v0))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                               (coe MAlonzo.Code.Once.TypeCheck.Context.d_name_14 (coe v3))) in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                         -> if coe v10
                              then coe
                                     seq (coe v11)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe MAlonzo.Code.Data.Fin.Base.C_zero_12) (coe v8)))
                              else coe
                                     seq (coe v11)
                                     (let v12 = coe du_go_960 (coe v0) (coe v4) (coe v6) in
                                      coe
                                        (case coe v12 of
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v13
                                             -> case coe v13 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                                                    -> coe
                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                            (coe
                                                               MAlonzo.Code.Data.Fin.Base.C_suc_16
                                                               v14)
                                                            (coe v15))
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v12
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.PolyBuiltinApp
d_PolyBuiltinApp_1024 = ()
data T_PolyBuiltinApp_1024
  = C_pba'45'id_1026 | C_pba'45'fst_1028 | C_pba'45'snd_1030 |
    C_pba'45'terminal_1032 | C_pba'45'inl_1034 | C_pba'45'inr_1036 |
    C_pba'45'initial_1038 | C_pba'45'pair'45'applied_1040 |
    C_pba'45'compose'45'applied_1042 | C_pba'45'case'45'applied_1044 |
    C_pba'45'curry_1046 | C_pba'45'apply_1048 | C_pba'45'In_1050 |
    C_pba'45'cata_1052
-- Once.TypeCheck.Classify.AppHeadView
d_AppHeadView_1054 a0 = ()
data T_AppHeadView_1054
  = C_ahv'45'id_1056 | C_ahv'45'fst_1058 | C_ahv'45'snd_1060 |
    C_ahv'45'terminal_1062 | C_ahv'45'inl_1064 | C_ahv'45'inr_1066 |
    C_ahv'45'initial_1068 | C_ahv'45'curry_1070 | C_ahv'45'apply_1072 |
    C_ahv'45'In_1074 | C_ahv'45'cata_1076 |
    C_ahv'45'pair'45'applied_1080 | C_ahv'45'compose'45'applied_1084 |
    C_ahv'45'case'45'applied_1088 | C_ahv'45'other_1092
-- Once.TypeCheck.Classify.classifyAppHeadView
d_classifyAppHeadView_1096 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_1054
d_classifyAppHeadView_1096 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> let v2
                 = coe
                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                     erased
                     (\ v2 ->
                        coe
                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                          (coe v1))
                     (coe
                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v1)
                        (coe ("id" :: Data.Text.Text))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v3 v4
                  -> if coe v3
                       then coe seq (coe v4) (coe C_ahv'45'id_1056)
                       else coe
                              seq (coe v4)
                              (let v5
                                     = coe
                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                         erased
                                         (\ v5 ->
                                            coe
                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                              (coe v1))
                                         (coe
                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                            (coe v1) (coe ("fst" :: Data.Text.Text))) in
                               coe
                                 (case coe v5 of
                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v6 v7
                                      -> if coe v6
                                           then coe seq (coe v7) (coe C_ahv'45'fst_1058)
                                           else coe
                                                  seq (coe v7)
                                                  (let v8
                                                         = coe
                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                             erased
                                                             (\ v8 ->
                                                                coe
                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                  (coe v1))
                                                             (coe
                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                (coe v1)
                                                                (coe ("snd" :: Data.Text.Text))) in
                                                   coe
                                                     (case coe v8 of
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                                          -> if coe v9
                                                               then coe
                                                                      seq (coe v10)
                                                                      (coe C_ahv'45'snd_1060)
                                                               else coe
                                                                      seq (coe v10)
                                                                      (let v11
                                                                             = coe
                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                 erased
                                                                                 (\ v11 ->
                                                                                    coe
                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                      (coe v1))
                                                                                 (coe
                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                    (coe v1)
                                                                                    (coe
                                                                                       ("terminal"
                                                                                        ::
                                                                                        Data.Text.Text))) in
                                                                       coe
                                                                         (case coe v11 of
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                                              -> if coe v12
                                                                                   then coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (coe
                                                                                             C_ahv'45'terminal_1062)
                                                                                   else coe
                                                                                          seq
                                                                                          (coe v13)
                                                                                          (let v14
                                                                                                 = coe
                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                     erased
                                                                                                     (\ v14 ->
                                                                                                        coe
                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                          (coe
                                                                                                             v1))
                                                                                                     (coe
                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                        (coe
                                                                                                           v1)
                                                                                                        (coe
                                                                                                           ("inl"
                                                                                                            ::
                                                                                                            Data.Text.Text))) in
                                                                                           coe
                                                                                             (case coe
                                                                                                     v14 of
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                                                  -> if coe
                                                                                                          v15
                                                                                                       then coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (coe
                                                                                                                 C_ahv'45'inl_1064)
                                                                                                       else coe
                                                                                                              seq
                                                                                                              (coe
                                                                                                                 v16)
                                                                                                              (let v17
                                                                                                                     = coe
                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                         erased
                                                                                                                         (\ v17 ->
                                                                                                                            coe
                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                              (coe
                                                                                                                                 v1))
                                                                                                                         (coe
                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                            (coe
                                                                                                                               v1)
                                                                                                                            (coe
                                                                                                                               ("inr"
                                                                                                                                ::
                                                                                                                                Data.Text.Text))) in
                                                                                                               coe
                                                                                                                 (case coe
                                                                                                                         v17 of
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                                                                                      -> if coe
                                                                                                                              v18
                                                                                                                           then coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (coe
                                                                                                                                     C_ahv'45'inr_1066)
                                                                                                                           else coe
                                                                                                                                  seq
                                                                                                                                  (coe
                                                                                                                                     v19)
                                                                                                                                  (let v20
                                                                                                                                         = coe
                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                             erased
                                                                                                                                             (\ v20 ->
                                                                                                                                                coe
                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                  (coe
                                                                                                                                                     v1))
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                (coe
                                                                                                                                                   v1)
                                                                                                                                                (coe
                                                                                                                                                   ("initial"
                                                                                                                                                    ::
                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                   coe
                                                                                                                                     (case coe
                                                                                                                                             v20 of
                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v21 v22
                                                                                                                                          -> if coe
                                                                                                                                                  v21
                                                                                                                                               then coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (coe
                                                                                                                                                         C_ahv'45'initial_1068)
                                                                                                                                               else coe
                                                                                                                                                      seq
                                                                                                                                                      (coe
                                                                                                                                                         v22)
                                                                                                                                                      (let v23
                                                                                                                                                             = coe
                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                 erased
                                                                                                                                                                 (\ v23 ->
                                                                                                                                                                    coe
                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                      (coe
                                                                                                                                                                         v1))
                                                                                                                                                                 (coe
                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                    (coe
                                                                                                                                                                       v1)
                                                                                                                                                                    (coe
                                                                                                                                                                       ("curry"
                                                                                                                                                                        ::
                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                       coe
                                                                                                                                                         (case coe
                                                                                                                                                                 v23 of
                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v24 v25
                                                                                                                                                              -> if coe
                                                                                                                                                                      v24
                                                                                                                                                                   then coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (coe
                                                                                                                                                                             C_ahv'45'curry_1070)
                                                                                                                                                                   else coe
                                                                                                                                                                          seq
                                                                                                                                                                          (coe
                                                                                                                                                                             v25)
                                                                                                                                                                          (let v26
                                                                                                                                                                                 = coe
                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                     erased
                                                                                                                                                                                     (\ v26 ->
                                                                                                                                                                                        coe
                                                                                                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                          (coe
                                                                                                                                                                                             v1))
                                                                                                                                                                                     (coe
                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                        (coe
                                                                                                                                                                                           v1)
                                                                                                                                                                                        (coe
                                                                                                                                                                                           ("apply"
                                                                                                                                                                                            ::
                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                           coe
                                                                                                                                                                             (case coe
                                                                                                                                                                                     v26 of
                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v27 v28
                                                                                                                                                                                  -> if coe
                                                                                                                                                                                          v27
                                                                                                                                                                                       then coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 C_ahv'45'apply_1072)
                                                                                                                                                                                       else coe
                                                                                                                                                                                              seq
                                                                                                                                                                                              (coe
                                                                                                                                                                                                 v28)
                                                                                                                                                                                              (let v29
                                                                                                                                                                                                     = coe
                                                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                         erased
                                                                                                                                                                                                         (\ v29 ->
                                                                                                                                                                                                            coe
                                                                                                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                 v1))
                                                                                                                                                                                                         (coe
                                                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               v1)
                                                                                                                                                                                                            (coe
                                                                                                                                                                                                               ("In"
                                                                                                                                                                                                                ::
                                                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                                                               coe
                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                         v29 of
                                                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v30 v31
                                                                                                                                                                                                      -> if coe
                                                                                                                                                                                                              v30
                                                                                                                                                                                                           then coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     C_ahv'45'In_1074)
                                                                                                                                                                                                           else coe
                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                     v31)
                                                                                                                                                                                                                  (let v32
                                                                                                                                                                                                                         = coe
                                                                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                             erased
                                                                                                                                                                                                                             (\ v32 ->
                                                                                                                                                                                                                                coe
                                                                                                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                     v1))
                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   v1)
                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                   ("cata"
                                                                                                                                                                                                                                    ::
                                                                                                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                                                                                                   coe
                                                                                                                                                                                                                     (case coe
                                                                                                                                                                                                                             v32 of
                                                                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v33 v34
                                                                                                                                                                                                                          -> if coe
                                                                                                                                                                                                                                  v33
                                                                                                                                                                                                                               then coe
                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v34)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         C_ahv'45'cata_1076)
                                                                                                                                                                                                                               else coe
                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v34)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         C_ahv'45'other_1092)
                                                                                                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                                            _ -> MAlonzo.RTE.mazUnreachableError))
                                                        _ -> MAlonzo.RTE.mazUnreachableError))
                                    _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v1
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
               -> let v4
                        = coe
                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                            erased
                            (\ v4 ->
                               coe
                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                 (coe v3))
                            (coe
                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v3)
                               (coe ("pair" :: Data.Text.Text))) in
                  coe
                    (case coe v4 of
                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                         -> if coe v5
                              then coe seq (coe v6) (coe C_ahv'45'pair'45'applied_1080)
                              else coe
                                     seq (coe v6)
                                     (let v7
                                            = coe
                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                erased
                                                (\ v7 ->
                                                   coe
                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                     (coe v3))
                                                (coe
                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                   (coe v3) (coe ("compose" :: Data.Text.Text))) in
                                      coe
                                        (case coe v7 of
                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                             -> if coe v8
                                                  then coe
                                                         seq (coe v9)
                                                         (coe C_ahv'45'compose'45'applied_1084)
                                                  else coe
                                                         seq (coe v9)
                                                         (let v10
                                                                = coe
                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                    erased
                                                                    (\ v10 ->
                                                                       coe
                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                         (coe v3))
                                                                    (coe
                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                       (coe v3)
                                                                       (coe
                                                                          ("case"
                                                                           ::
                                                                           Data.Text.Text))) in
                                                          coe
                                                            (case coe v10 of
                                                               MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                 -> if coe v11
                                                                      then coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                C_ahv'45'case'45'applied_1088)
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                C_ahv'45'other_1092)
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v3
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v3 v4
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v3 v4
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v3 v4 v5
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v3 v4
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v3
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v3 v4 v5 v6
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v3
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v3 v4
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v3 v4 v5
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v4
               -> coe C_ahv'45'other_1092
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v3 v4
               -> coe C_ahv'45'other_1092
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v1 v2
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v1 v2 v3
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v1 v2
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v1
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v1 v2 v3 v4
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v1
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v1 v2
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v1 v2 v3
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v2
        -> coe C_ahv'45'other_1092
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v1 v2
        -> coe C_ahv'45'other_1092
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.viewToPba
d_viewToPba_1216 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_AppHeadView_1054 -> Maybe T_PolyBuiltinApp_1024
d_viewToPba_1216 ~v0 v1 = du_viewToPba_1216 v1
du_viewToPba_1216 ::
  T_AppHeadView_1054 -> Maybe T_PolyBuiltinApp_1024
du_viewToPba_1216 v0
  = case coe v0 of
      C_ahv'45'id_1056
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_1026)
      C_ahv'45'fst_1058
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'fst_1028)
      C_ahv'45'snd_1060
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'snd_1030)
      C_ahv'45'terminal_1062
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'terminal_1032)
      C_ahv'45'inl_1064
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inl_1034)
      C_ahv'45'inr_1066
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inr_1036)
      C_ahv'45'initial_1068
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'initial_1038)
      C_ahv'45'curry_1070
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'curry_1046)
      C_ahv'45'apply_1072
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'apply_1048)
      C_ahv'45'In_1074
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'In_1050)
      C_ahv'45'cata_1076
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'cata_1052)
      C_ahv'45'pair'45'applied_1080
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'pair'45'applied_1040)
      C_ahv'45'compose'45'applied_1084
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'compose'45'applied_1042)
      C_ahv'45'case'45'applied_1088
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'case'45'applied_1044)
      C_ahv'45'other_1092
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.classifyAppHead
d_classifyAppHead_1218 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_1024
d_classifyAppHead_1218 v0
  = coe du_viewToPba_1216 (coe d_classifyAppHeadView_1096 (coe v0))
-- Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_1224 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_1224 = erased
-- Once.TypeCheck.Classify.view-other⇒classifyAppHead-nothing
d_view'45'other'8658'classifyAppHead'45'nothing_1296 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_view'45'other'8658'classifyAppHead'45'nothing_1296 = erased
-- Once.TypeCheck.Classify.BareBuiltinClass
d_BareBuiltinClass_1306 a0 = ()
data T_BareBuiltinClass_1306
  = C_bbc'45'id_1308 | C_bbc'45'fst_1310 | C_bbc'45'snd_1312 |
    C_bbc'45'terminal_1314 | C_bbc'45'initial_1316 |
    C_bbc'45'inl_1318 | C_bbc'45'inr_1320 | C_bbc'45'other_1324
-- Once.TypeCheck.Classify.classifyBareBuiltin
d_classifyBareBuiltin_1328 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_BareBuiltinClass_1306
d_classifyBareBuiltin_1328 v0
  = let v1
          = coe
              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
              erased
              (\ v1 ->
                 coe
                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                   (coe v0))
              (coe
                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                 (coe ("id" :: Data.Text.Text))) in
    coe
      (case coe v1 of
         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v2 v3
           -> if coe v2
                then coe seq (coe v3) (coe C_bbc'45'id_1308)
                else coe
                       seq (coe v3)
                       (let v4
                              = coe
                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                  erased
                                  (\ v4 ->
                                     coe
                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                       (coe v0))
                                  (coe
                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28 (coe v0)
                                     (coe ("fst" :: Data.Text.Text))) in
                        coe
                          (case coe v4 of
                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v5 v6
                               -> if coe v5
                                    then coe seq (coe v6) (coe C_bbc'45'fst_1310)
                                    else coe
                                           seq (coe v6)
                                           (let v7
                                                  = coe
                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                      erased
                                                      (\ v7 ->
                                                         coe
                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                           (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                         (coe v0)
                                                         (coe ("snd" :: Data.Text.Text))) in
                                            coe
                                              (case coe v7 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                                   -> if coe v8
                                                        then coe
                                                               seq (coe v9) (coe C_bbc'45'snd_1312)
                                                        else coe
                                                               seq (coe v9)
                                                               (let v10
                                                                      = coe
                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                          erased
                                                                          (\ v10 ->
                                                                             coe
                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                               (coe v0))
                                                                          (coe
                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                             (coe v0)
                                                                             (coe
                                                                                ("terminal"
                                                                                 ::
                                                                                 Data.Text.Text))) in
                                                                coe
                                                                  (case coe v10 of
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                       -> if coe v11
                                                                            then coe
                                                                                   seq (coe v12)
                                                                                   (coe
                                                                                      C_bbc'45'terminal_1314)
                                                                            else coe
                                                                                   seq (coe v12)
                                                                                   (let v13
                                                                                          = coe
                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                              erased
                                                                                              (\ v13 ->
                                                                                                 coe
                                                                                                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                   (coe
                                                                                                      v0))
                                                                                              (coe
                                                                                                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                 (coe
                                                                                                    v0)
                                                                                                 (coe
                                                                                                    ("initial"
                                                                                                     ::
                                                                                                     Data.Text.Text))) in
                                                                                    coe
                                                                                      (case coe
                                                                                              v13 of
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v14 v15
                                                                                           -> if coe
                                                                                                   v14
                                                                                                then coe
                                                                                                       seq
                                                                                                       (coe
                                                                                                          v15)
                                                                                                       (coe
                                                                                                          C_bbc'45'initial_1316)
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
                                                                                                                          v0))
                                                                                                                  (coe
                                                                                                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                     (coe
                                                                                                                        v0)
                                                                                                                     (coe
                                                                                                                        ("inl"
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
                                                                                                                              C_bbc'45'inl_1318)
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
                                                                                                                                              v0))
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                         (coe
                                                                                                                                            v0)
                                                                                                                                         (coe
                                                                                                                                            ("inr"
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
                                                                                                                                                  C_bbc'45'inr_1320)
                                                                                                                                        else coe
                                                                                                                                               seq
                                                                                                                                               (coe
                                                                                                                                                  v21)
                                                                                                                                               (coe
                                                                                                                                                  C_bbc'45'other_1324)
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.ViewBundle
d_ViewBundle_1388 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_ViewBundle_1388 = erased
-- Once.TypeCheck.Classify.viewBundle
d_viewBundle_1396 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_1396 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_classifyAppHeadView_1096 (coe v0)) erased
