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
import qualified MAlonzo.Code.Data.List.Properties
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
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
import qualified MAlonzo.Code.Relation.Nullary.Reflects

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
-- Once.TypeCheck.Classify.composeArgB-res
d_composeArgB'45'res_734 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB'45'res_734 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.CanonicalName.C_canonical_10 v3
        -> case coe v3 of
             []
               -> coe
                    d_composeArgB'45'lookup_670 (coe v0)
                    (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                    (coe v2)
             (:) v4 v5
               -> case coe v5 of
                    []
                      -> coe
                           d_composeArgB'45'lookup_670 (coe v0)
                           (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                           (coe v2)
                    (:) v6 v7
                      -> case coe v7 of
                           []
                             -> let v8
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v8 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v4))
                                          (coe
                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                             (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.CanonicalName.d_generatorNS_16)) in
                                coe
                                  (case coe v8 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v9 v10
                                       -> if coe v9
                                            then coe
                                                   seq (coe v10)
                                                   (let v11
                                                          = coe
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                              erased
                                                              (\ v11 ->
                                                                 coe
                                                                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                   (coe v6))
                                                              (coe
                                                                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                 (coe v6)
                                                                 (coe ("fst" :: Data.Text.Text))) in
                                                    coe
                                                      (case coe v11 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v12 v13
                                                           -> if coe v12
                                                                then coe
                                                                       seq (coe v13)
                                                                       (coe
                                                                          d_composeArgB'45'fst_714
                                                                          (coe v0) (coe v2))
                                                                else coe
                                                                       seq (coe v13)
                                                                       (let v14
                                                                              = coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                  erased
                                                                                  (\ v14 ->
                                                                                     coe
                                                                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                       (coe v6))
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                     (coe v6)
                                                                                     (coe
                                                                                        ("snd"
                                                                                         ::
                                                                                         Data.Text.Text))) in
                                                                        coe
                                                                          (case coe v14 of
                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v15 v16
                                                                               -> if coe v15
                                                                                    then coe
                                                                                           seq
                                                                                           (coe v16)
                                                                                           (coe
                                                                                              d_composeArgB'45'snd_724
                                                                                              (coe
                                                                                                 v0)
                                                                                              (coe
                                                                                                 v2))
                                                                                    else coe
                                                                                           seq
                                                                                           (coe v16)
                                                                                           (let v17
                                                                                                  = coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                      erased
                                                                                                      (\ v17 ->
                                                                                                         coe
                                                                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                           (coe
                                                                                                              v6))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                         (coe
                                                                                                            v6)
                                                                                                         (coe
                                                                                                            ("id"
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
                                                                                                                  MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                  (coe
                                                                                                                     v2))
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
                                                                                                                                  v6))
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                             (coe
                                                                                                                                v6)
                                                                                                                             (coe
                                                                                                                                ("terminal"
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
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Once.Type.C_Unit_118))
                                                                                                                            else coe
                                                                                                                                   seq
                                                                                                                                   (coe
                                                                                                                                      v22)
                                                                                                                                   (coe
                                                                                                                                      d_composeArgB'45'lookup_670
                                                                                                                                      (coe
                                                                                                                                         v0)
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Once.CanonicalName.d_showCanonical_134
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Once.CanonicalName.C_canonical_10
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                                                                                                               (coe
                                                                                                                                                  ("Generators"
                                                                                                                                                   ::
                                                                                                                                                   Data.Text.Text))
                                                                                                                                               (coe
                                                                                                                                                  v5))))
                                                                                                                                      (coe
                                                                                                                                         v2))
                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                            else coe
                                                   seq (coe v10)
                                                   (coe
                                                      d_composeArgB'45'lookup_670 (coe v0)
                                                      (coe
                                                         MAlonzo.Code.Once.CanonicalName.d_showCanonical_134
                                                         (coe v1))
                                                      (coe v2))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           (:) v8 v9
                             -> coe
                                  d_composeArgB'45'lookup_670 (coe v0)
                                  (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v1))
                                  (coe v2)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.composeArgB
d_composeArgB_866 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB_866 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> coe d_composeArgB'45'lookup_670 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4
           -> coe d_composeArgB'45'res_734 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v8
                         -> let v9
                                  = coe
                                      MAlonzo.Code.Data.List.Properties.du_'8801''45'dec_60
                                      (coe MAlonzo.Code.Data.String.Properties.d__'8799'__54)
                                      (coe MAlonzo.Code.Once.CanonicalName.d_parts_8 (coe v8))
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                         (coe ("Generators" :: Data.Text.Text))
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                            (coe ("compose" :: Data.Text.Text))
                                            (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16))) in
                            coe
                              (case coe v9 of
                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                   -> if coe v10
                                        then let v12
                                                   = seq
                                                       (coe v11)
                                                       (coe
                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                          (coe v10)
                                                          (coe
                                                             MAlonzo.Code.Relation.Nullary.Reflects.C_of'696'_22
                                                             erased)) in
                                             coe
                                               (case coe v12 of
                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                    -> if coe v13
                                                         then coe
                                                                seq (coe v14)
                                                                (let v15
                                                                       = d_composeArgB_866
                                                                           (coe v0) (coe v5)
                                                                           (coe v2) in
                                                                 coe
                                                                   (case coe v15 of
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                        -> coe
                                                                             d_composeArgB_866
                                                                             (coe v0) (coe v7)
                                                                             (coe v16)
                                                                      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                        -> coe v15
                                                                      _ -> MAlonzo.RTE.mazUnreachableError))
                                                         else coe
                                                                seq (coe v14)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                  _ -> MAlonzo.RTE.mazUnreachableError)
                                        else (let v12
                                                    = seq
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Relation.Nullary.Reflects.C_of'8319'_26)) in
                                              coe
                                                (case coe v12 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                     -> if coe v13
                                                          then coe
                                                                 seq (coe v14)
                                                                 (let v15
                                                                        = d_composeArgB_866
                                                                            (coe v0) (coe v5)
                                                                            (coe v2) in
                                                                  coe
                                                                    (case coe v15 of
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                                                         -> coe
                                                                              d_composeArgB_866
                                                                              (coe v0) (coe v7)
                                                                              (coe v16)
                                                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                                         -> coe v15
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          else coe
                                                                 seq (coe v14)
                                                                 (coe
                                                                    MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                   _ -> MAlonzo.RTE.mazUnreachableError))
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v4 v5
           -> case coe v5 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_Unit_118)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_Int_132)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v6 v7 v8 v9
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_Float_134)
                MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v6
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                       (coe MAlonzo.Code.Once.Type.C_Str_136)
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.Type.C_Int_132)
         _ -> coe v3)
-- Once.TypeCheck.Classify.domainOfHead-arrow
d_domainOfHead'45'arrow_980 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_domainOfHead'45'arrow_980 v0
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
d_domainOfHead_984 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_domainOfHead_984 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
           -> coe
                d_domainOfHead'45'arrow_980
                (coe d_lookupImport_442 (coe d_imports_362 (coe v0)) (coe v3))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v3
           -> coe
                d_domainOfHead'45'arrow_980
                (coe
                   d_lookupImport_442 (coe d_imports_362 (coe v0))
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_134 (coe v3)))
         _ -> coe v2)
-- Once.TypeCheck.Classify.composeMid-pick
d_composeMid'45'pick_994 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeMid'45'pick_994 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.composeMid
d_composeMid_1000 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeMid_1000 v0 v1 v2 v3
  = coe
      d_composeMid'45'pick_994
      (coe d_composeArgB_866 (coe v0) (coe v2) (coe v3))
      (coe d_domainOfHead_984 (coe v0) (coe v1))
-- Once.TypeCheck.Classify.findLocalVarUsage
d_findLocalVarUsage_1012 ::
  T_NamedCtx_338 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_1012 v0 v1
  = case coe v0 of
      C_mkCtx_368 v2 v3 v4 v5 v6 v7 v8
        -> coe du_go_1028 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.go
d_go_1028 ::
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
d_go_1028 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10
  = du_go_1028 v7 v9 v10
du_go_1028 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_1028 v0 v1 v2
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
                                     (let v12 = coe du_go_1028 (coe v0) (coe v4) (coe v6) in
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
d_PolyBuiltinApp_1092 = ()
data T_PolyBuiltinApp_1092
  = C_pba'45'id_1094 | C_pba'45'fst_1096 | C_pba'45'snd_1098 |
    C_pba'45'terminal_1100 | C_pba'45'inl_1102 | C_pba'45'inr_1104 |
    C_pba'45'initial_1106 | C_pba'45'pair'45'applied_1108 |
    C_pba'45'compose'45'applied_1110 | C_pba'45'case'45'applied_1112 |
    C_pba'45'curry_1114 | C_pba'45'apply_1116 | C_pba'45'In_1118 |
    C_pba'45'cata_1120
-- Once.TypeCheck.Classify.AppHeadView
d_AppHeadView_1122 a0 = ()
data T_AppHeadView_1122
  = C_ahv'45'id_1124 | C_ahv'45'fst_1126 | C_ahv'45'snd_1128 |
    C_ahv'45'terminal_1130 | C_ahv'45'inl_1132 | C_ahv'45'inr_1134 |
    C_ahv'45'initial_1136 | C_ahv'45'curry_1138 | C_ahv'45'apply_1140 |
    C_ahv'45'In_1142 | C_ahv'45'cata_1144 |
    C_ahv'45'pair'45'applied_1148 | C_ahv'45'compose'45'applied_1152 |
    C_ahv'45'case'45'applied_1156 | C_ahv'45'other_1160
-- Once.TypeCheck.Classify.classifyAppHeadView
d_classifyAppHeadView_1164 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_1122
d_classifyAppHeadView_1164 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CanonicalName.C_canonical_10 v2
               -> case coe v2 of
                    [] -> coe C_ahv'45'other_1160
                    (:) v3 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_1160
                           (:) v5 v6
                             -> case coe v6 of
                                  []
                                    -> let v7
                                             = coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                 erased
                                                 (\ v7 ->
                                                    coe
                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                      (coe v3))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                    (coe v3)
                                                    (coe
                                                       MAlonzo.Code.Once.CanonicalName.d_generatorNS_16)) in
                                       coe
                                         (case coe v7 of
                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v8 v9
                                              -> if coe v8
                                                   then coe
                                                          seq (coe v9)
                                                          (let v10
                                                                 = coe
                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                     erased
                                                                     (\ v10 ->
                                                                        coe
                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                          (coe v5))
                                                                     (coe
                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                        (coe v5)
                                                                        (coe
                                                                           ("id"
                                                                            ::
                                                                            Data.Text.Text))) in
                                                           coe
                                                             (case coe v10 of
                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v11 v12
                                                                  -> if coe v11
                                                                       then coe
                                                                              seq (coe v12)
                                                                              (coe C_ahv'45'id_1124)
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
                                                                                                 v5))
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                            (coe v5)
                                                                                            (coe
                                                                                               ("fst"
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
                                                                                                     C_ahv'45'fst_1126)
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
                                                                                                                     v5))
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                (coe
                                                                                                                   v5)
                                                                                                                (coe
                                                                                                                   ("snd"
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
                                                                                                                         C_ahv'45'snd_1128)
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
                                                                                                                                         v5))
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                    (coe
                                                                                                                                       v5)
                                                                                                                                    (coe
                                                                                                                                       ("terminal"
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
                                                                                                                                             C_ahv'45'terminal_1130)
                                                                                                                                   else coe
                                                                                                                                          seq
                                                                                                                                          (coe
                                                                                                                                             v21)
                                                                                                                                          (let v22
                                                                                                                                                 = coe
                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                     erased
                                                                                                                                                     (\ v22 ->
                                                                                                                                                        coe
                                                                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                          (coe
                                                                                                                                                             v5))
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                        (coe
                                                                                                                                                           v5)
                                                                                                                                                        (coe
                                                                                                                                                           ("inl"
                                                                                                                                                            ::
                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                           coe
                                                                                                                                             (case coe
                                                                                                                                                     v22 of
                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v23 v24
                                                                                                                                                  -> if coe
                                                                                                                                                          v23
                                                                                                                                                       then coe
                                                                                                                                                              seq
                                                                                                                                                              (coe
                                                                                                                                                                 v24)
                                                                                                                                                              (coe
                                                                                                                                                                 C_ahv'45'inl_1132)
                                                                                                                                                       else coe
                                                                                                                                                              seq
                                                                                                                                                              (coe
                                                                                                                                                                 v24)
                                                                                                                                                              (let v25
                                                                                                                                                                     = coe
                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                         erased
                                                                                                                                                                         (\ v25 ->
                                                                                                                                                                            coe
                                                                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                              (coe
                                                                                                                                                                                 v5))
                                                                                                                                                                         (coe
                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                            (coe
                                                                                                                                                                               v5)
                                                                                                                                                                            (coe
                                                                                                                                                                               ("inr"
                                                                                                                                                                                ::
                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                               coe
                                                                                                                                                                 (case coe
                                                                                                                                                                         v25 of
                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v26 v27
                                                                                                                                                                      -> if coe
                                                                                                                                                                              v26
                                                                                                                                                                           then coe
                                                                                                                                                                                  seq
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v27)
                                                                                                                                                                                  (coe
                                                                                                                                                                                     C_ahv'45'inr_1134)
                                                                                                                                                                           else coe
                                                                                                                                                                                  seq
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v27)
                                                                                                                                                                                  (let v28
                                                                                                                                                                                         = coe
                                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                             erased
                                                                                                                                                                                             (\ v28 ->
                                                                                                                                                                                                coe
                                                                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                  (coe
                                                                                                                                                                                                     v5))
                                                                                                                                                                                             (coe
                                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   v5)
                                                                                                                                                                                                (coe
                                                                                                                                                                                                   ("initial"
                                                                                                                                                                                                    ::
                                                                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                                                                   coe
                                                                                                                                                                                     (case coe
                                                                                                                                                                                             v28 of
                                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v29 v30
                                                                                                                                                                                          -> if coe
                                                                                                                                                                                                  v29
                                                                                                                                                                                               then coe
                                                                                                                                                                                                      seq
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         v30)
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         C_ahv'45'initial_1136)
                                                                                                                                                                                               else coe
                                                                                                                                                                                                      seq
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         v30)
                                                                                                                                                                                                      (let v31
                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                 erased
                                                                                                                                                                                                                 (\ v31 ->
                                                                                                                                                                                                                    coe
                                                                                                                                                                                                                      MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                         v5))
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       v5)
                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                       ("curry"
                                                                                                                                                                                                                        ::
                                                                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                                                                       coe
                                                                                                                                                                                                         (case coe
                                                                                                                                                                                                                 v31 of
                                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v32 v33
                                                                                                                                                                                                              -> if coe
                                                                                                                                                                                                                      v32
                                                                                                                                                                                                                   then coe
                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             v33)
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             C_ahv'45'curry_1138)
                                                                                                                                                                                                                   else coe
                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             v33)
                                                                                                                                                                                                                          (let v34
                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                     erased
                                                                                                                                                                                                                                     (\ v34 ->
                                                                                                                                                                                                                                        coe
                                                                                                                                                                                                                                          MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                             v5))
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                           v5)
                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                           ("apply"
                                                                                                                                                                                                                                            ::
                                                                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                             (case coe
                                                                                                                                                                                                                                     v34 of
                                                                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v35 v36
                                                                                                                                                                                                                                  -> if coe
                                                                                                                                                                                                                                          v35
                                                                                                                                                                                                                                       then coe
                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 v36)
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 C_ahv'45'apply_1140)
                                                                                                                                                                                                                                       else coe
                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 v36)
                                                                                                                                                                                                                                              (let v37
                                                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                         erased
                                                                                                                                                                                                                                                         (\ v37 ->
                                                                                                                                                                                                                                                            coe
                                                                                                                                                                                                                                                              MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                 v5))
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               v5)
                                                                                                                                                                                                                                                            (coe
                                                                                                                                                                                                                                                               ("In"
                                                                                                                                                                                                                                                                ::
                                                                                                                                                                                                                                                                Data.Text.Text))) in
                                                                                                                                                                                                                                               coe
                                                                                                                                                                                                                                                 (case coe
                                                                                                                                                                                                                                                         v37 of
                                                                                                                                                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v38 v39
                                                                                                                                                                                                                                                      -> if coe
                                                                                                                                                                                                                                                              v38
                                                                                                                                                                                                                                                           then coe
                                                                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v39)
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     C_ahv'45'In_1142)
                                                                                                                                                                                                                                                           else coe
                                                                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v39)
                                                                                                                                                                                                                                                                  (let v40
                                                                                                                                                                                                                                                                         = coe
                                                                                                                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                                             erased
                                                                                                                                                                                                                                                                             (\ v40 ->
                                                                                                                                                                                                                                                                                coe
                                                                                                                                                                                                                                                                                  MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                                     v5))
                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                   v5)
                                                                                                                                                                                                                                                                                (coe
                                                                                                                                                                                                                                                                                   ("cata"
                                                                                                                                                                                                                                                                                    ::
                                                                                                                                                                                                                                                                                    Data.Text.Text))) in
                                                                                                                                                                                                                                                                   coe
                                                                                                                                                                                                                                                                     (case coe
                                                                                                                                                                                                                                                                             v40 of
                                                                                                                                                                                                                                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v41 v42
                                                                                                                                                                                                                                                                          -> if coe
                                                                                                                                                                                                                                                                                  v41
                                                                                                                                                                                                                                                                               then coe
                                                                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         v42)
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         C_ahv'45'cata_1144)
                                                                                                                                                                                                                                                                               else coe
                                                                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         v42)
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         C_ahv'45'other_1160)
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
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   else coe seq (coe v9) (coe C_ahv'45'other_1160)
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  (:) v7 v8 -> coe C_ahv'45'other_1160
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v3
               -> case coe v3 of
                    MAlonzo.Code.Once.CanonicalName.C_canonical_10 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_1160
                           (:) v5 v6
                             -> case coe v6 of
                                  [] -> coe C_ahv'45'other_1160
                                  (:) v7 v8
                                    -> case coe v8 of
                                         []
                                           -> let v9
                                                    = coe
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                        erased
                                                        (\ v9 ->
                                                           coe
                                                             MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                             (coe v5))
                                                        (coe
                                                           MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                           (coe v5)
                                                           (coe
                                                              MAlonzo.Code.Once.CanonicalName.d_generatorNS_16)) in
                                              coe
                                                (case coe v9 of
                                                   MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                     -> if coe v10
                                                          then coe
                                                                 seq (coe v11)
                                                                 (let v12
                                                                        = coe
                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                            erased
                                                                            (\ v12 ->
                                                                               coe
                                                                                 MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                 (coe v7))
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                               (coe v7)
                                                                               (coe
                                                                                  ("pair"
                                                                                   ::
                                                                                   Data.Text.Text))) in
                                                                  coe
                                                                    (case coe v12 of
                                                                       MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v13 v14
                                                                         -> if coe v13
                                                                              then coe
                                                                                     seq (coe v14)
                                                                                     (coe
                                                                                        C_ahv'45'pair'45'applied_1148)
                                                                              else coe
                                                                                     seq (coe v14)
                                                                                     (let v15
                                                                                            = coe
                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                erased
                                                                                                (\ v15 ->
                                                                                                   coe
                                                                                                     MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                     (coe
                                                                                                        v7))
                                                                                                (coe
                                                                                                   MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                   (coe
                                                                                                      v7)
                                                                                                   (coe
                                                                                                      ("compose"
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
                                                                                                            C_ahv'45'compose'45'applied_1152)
                                                                                                  else coe
                                                                                                         seq
                                                                                                         (coe
                                                                                                            v17)
                                                                                                         (let v18
                                                                                                                = coe
                                                                                                                    MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                    erased
                                                                                                                    (\ v18 ->
                                                                                                                       coe
                                                                                                                         MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                         (coe
                                                                                                                            v7))
                                                                                                                    (coe
                                                                                                                       MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                       (coe
                                                                                                                          v7)
                                                                                                                       (coe
                                                                                                                          ("case"
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
                                                                                                                                C_ahv'45'case'45'applied_1156)
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v20)
                                                                                                                             (coe
                                                                                                                                C_ahv'45'other_1160)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          else coe
                                                                 seq (coe v11)
                                                                 (coe C_ahv'45'other_1160)
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         (:) v9 v10 -> coe C_ahv'45'other_1160
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v3 v4
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v3 v4
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v3 v4 v5
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v3 v4
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v3
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v3 v4 v5 v6
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v3
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v3 v4
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v3 v4 v5
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v4
               -> coe C_ahv'45'other_1160
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v3 v4
               -> coe C_ahv'45'other_1160
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v1 v2
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v1 v2 v3
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v1 v2
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v1
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v1 v2 v3 v4
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v1
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v1 v2
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v1 v2 v3
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v2
        -> coe C_ahv'45'other_1160
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v1 v2
        -> coe C_ahv'45'other_1160
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.viewToPba
d_viewToPba_1368 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_AppHeadView_1122 -> Maybe T_PolyBuiltinApp_1092
d_viewToPba_1368 ~v0 v1 = du_viewToPba_1368 v1
du_viewToPba_1368 ::
  T_AppHeadView_1122 -> Maybe T_PolyBuiltinApp_1092
du_viewToPba_1368 v0
  = case coe v0 of
      C_ahv'45'id_1124
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_1094)
      C_ahv'45'fst_1126
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'fst_1096)
      C_ahv'45'snd_1128
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'snd_1098)
      C_ahv'45'terminal_1130
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'terminal_1100)
      C_ahv'45'inl_1132
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inl_1102)
      C_ahv'45'inr_1134
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inr_1104)
      C_ahv'45'initial_1136
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'initial_1106)
      C_ahv'45'curry_1138
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'curry_1114)
      C_ahv'45'apply_1140
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'apply_1116)
      C_ahv'45'In_1142
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'In_1118)
      C_ahv'45'cata_1144
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'cata_1120)
      C_ahv'45'pair'45'applied_1148
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'pair'45'applied_1108)
      C_ahv'45'compose'45'applied_1152
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'compose'45'applied_1110)
      C_ahv'45'case'45'applied_1156
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'case'45'applied_1112)
      C_ahv'45'other_1160
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.classifyAppHead
d_classifyAppHead_1370 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_1092
d_classifyAppHead_1370 v0
  = coe du_viewToPba_1368 (coe d_classifyAppHeadView_1164 (coe v0))
-- Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_1376 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_1376 = erased
-- Once.TypeCheck.Classify.view-other⇒classifyAppHead-nothing
d_view'45'other'8658'classifyAppHead'45'nothing_1448 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_view'45'other'8658'classifyAppHead'45'nothing_1448 = erased
-- Once.TypeCheck.Classify.GenView
d_GenView_1458 a0 = ()
data T_GenView_1458
  = C_gv'45'id_1460 | C_gv'45'fst_1462 | C_gv'45'snd_1464 |
    C_gv'45'terminal_1466 | C_gv'45'initial_1468 | C_gv'45'inl_1470 |
    C_gv'45'inr_1472 | C_gv'45'unit_1474 |
    C_gv'45'other_1478 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.TypeCheck.Classify.notGen-ns
d_notGen'45'ns_1484 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_notGen'45'ns_1484 ~v0 ~v1 ~v2 = du_notGen'45'ns_1484
du_notGen'45'ns_1484 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_notGen'45'ns_1484
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
d_f_1498 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_f_1498 = erased
-- Once.TypeCheck.Classify.notGen-shape
d_notGen'45'shape_1504 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_notGen'45'shape_1504 ~v0 v1 = du_notGen'45'shape_1504 v1
du_notGen'45'shape_1504 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_notGen'45'shape_1504 v0
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
d_classifyGen_1510 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> T_GenView_1458
d_classifyGen_1510 v0
  = case coe v0 of
      MAlonzo.Code.Once.CanonicalName.C_canonical_10 v1
        -> case coe v1 of
             [] -> coe C_gv'45'other_1478 (coe du_notGen'45'shape_1504 erased)
             (:) v2 v3
               -> case coe v3 of
                    [] -> coe C_gv'45'other_1478 (coe du_notGen'45'shape_1504 erased)
                    (:) v4 v5
                      -> case coe v5 of
                           []
                             -> let v6
                                      = coe
                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                          erased
                                          (\ v6 ->
                                             coe
                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                               (coe v2))
                                          (coe
                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                             (coe v2)
                                             (coe
                                                MAlonzo.Code.Once.CanonicalName.d_generatorNS_16)) in
                                coe
                                  (case coe v6 of
                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v7 v8
                                       -> if coe v7
                                            then coe
                                                   seq (coe v8)
                                                   (let v9
                                                          = coe
                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                              erased
                                                              (\ v9 ->
                                                                 coe
                                                                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                   (coe v4))
                                                              (coe
                                                                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                 (coe v4)
                                                                 (coe ("id" :: Data.Text.Text))) in
                                                    coe
                                                      (case coe v9 of
                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v10 v11
                                                           -> if coe v10
                                                                then coe
                                                                       seq (coe v11)
                                                                       (coe C_gv'45'id_1460)
                                                                else coe
                                                                       seq (coe v11)
                                                                       (let v12
                                                                              = coe
                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                  erased
                                                                                  (\ v12 ->
                                                                                     coe
                                                                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                       (coe v4))
                                                                                  (coe
                                                                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
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
                                                                                              C_gv'45'fst_1462)
                                                                                    else coe
                                                                                           seq
                                                                                           (coe v14)
                                                                                           (let v15
                                                                                                  = coe
                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                      erased
                                                                                                      (\ v15 ->
                                                                                                         coe
                                                                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                           (coe
                                                                                                              v4))
                                                                                                      (coe
                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
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
                                                                                                                  C_gv'45'snd_1464)
                                                                                                        else coe
                                                                                                               seq
                                                                                                               (coe
                                                                                                                  v17)
                                                                                                               (let v18
                                                                                                                      = coe
                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                          erased
                                                                                                                          (\ v18 ->
                                                                                                                             coe
                                                                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                               (coe
                                                                                                                                  v4))
                                                                                                                          (coe
                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
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
                                                                                                                                      C_gv'45'terminal_1466)
                                                                                                                            else coe
                                                                                                                                   seq
                                                                                                                                   (coe
                                                                                                                                      v20)
                                                                                                                                   (let v21
                                                                                                                                          = coe
                                                                                                                                              MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                              erased
                                                                                                                                              (\ v21 ->
                                                                                                                                                 coe
                                                                                                                                                   MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                   (coe
                                                                                                                                                      v4))
                                                                                                                                              (coe
                                                                                                                                                 MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
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
                                                                                                                                                          C_gv'45'initial_1468)
                                                                                                                                                else coe
                                                                                                                                                       seq
                                                                                                                                                       (coe
                                                                                                                                                          v23)
                                                                                                                                                       (let v24
                                                                                                                                                              = coe
                                                                                                                                                                  MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                  erased
                                                                                                                                                                  (\ v24 ->
                                                                                                                                                                     coe
                                                                                                                                                                       MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                       (coe
                                                                                                                                                                          v4))
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
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
                                                                                                                                                                              C_gv'45'inl_1470)
                                                                                                                                                                    else coe
                                                                                                                                                                           seq
                                                                                                                                                                           (coe
                                                                                                                                                                              v26)
                                                                                                                                                                           (let v27
                                                                                                                                                                                  = coe
                                                                                                                                                                                      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                      erased
                                                                                                                                                                                      (\ v27 ->
                                                                                                                                                                                         coe
                                                                                                                                                                                           MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                           (coe
                                                                                                                                                                                              v4))
                                                                                                                                                                                      (coe
                                                                                                                                                                                         MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
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
                                                                                                                                                                                                  C_gv'45'inr_1472)
                                                                                                                                                                                        else coe
                                                                                                                                                                                               seq
                                                                                                                                                                                               (coe
                                                                                                                                                                                                  v29)
                                                                                                                                                                                               (let v30
                                                                                                                                                                                                      = coe
                                                                                                                                                                                                          MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                          erased
                                                                                                                                                                                                          (\ v30 ->
                                                                                                                                                                                                             coe
                                                                                                                                                                                                               MAlonzo.Code.Data.String.Properties.du_'8776''45'reflexive_8
                                                                                                                                                                                                               (coe
                                                                                                                                                                                                                  v4))
                                                                                                                                                                                                          (coe
                                                                                                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
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
                                                                                                                                                                                                                      C_gv'45'unit_1474)
                                                                                                                                                                                                            else coe
                                                                                                                                                                                                                   seq
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      v32)
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      C_gv'45'other_1478
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
                                                   (coe
                                                      C_gv'45'other_1478 (coe du_notGen'45'ns_1484))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           (:) v6 v7
                             -> coe C_gv'45'other_1478 (coe du_notGen'45'shape_1504 erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.BareBuiltinClass
d_BareBuiltinClass_1770 a0 = ()
data T_BareBuiltinClass_1770
  = C_bbc'45'id_1772 | C_bbc'45'fst_1774 | C_bbc'45'snd_1776 |
    C_bbc'45'terminal_1778 | C_bbc'45'initial_1780 |
    C_bbc'45'inl_1782 | C_bbc'45'inr_1784 | C_bbc'45'other_1788
-- Once.TypeCheck.Classify.classifyBareBuiltin
d_classifyBareBuiltin_1792 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_BareBuiltinClass_1770
d_classifyBareBuiltin_1792 v0
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
                then coe seq (coe v3) (coe C_bbc'45'id_1772)
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
                                    then coe seq (coe v6) (coe C_bbc'45'fst_1774)
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
                                                               seq (coe v9) (coe C_bbc'45'snd_1776)
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
                                                                                      C_bbc'45'terminal_1778)
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
                                                                                                          C_bbc'45'initial_1780)
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
                                                                                                                              C_bbc'45'inl_1782)
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
                                                                                                                                                  C_bbc'45'inr_1784)
                                                                                                                                        else coe
                                                                                                                                               seq
                                                                                                                                               (coe
                                                                                                                                                  v21)
                                                                                                                                               (coe
                                                                                                                                                  C_bbc'45'other_1788)
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.ViewBundle
d_ViewBundle_1852 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_ViewBundle_1852 = erased
-- Once.TypeCheck.Classify.viewBundle
d_viewBundle_1860 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_1860 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_classifyAppHeadView_1164 (coe v0)) erased
