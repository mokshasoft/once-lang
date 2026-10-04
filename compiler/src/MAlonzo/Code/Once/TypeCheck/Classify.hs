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
import qualified MAlonzo.Code.Data.Nat.Show
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.String.Properties
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.Classify._≟ₛ_
d__'8799''8347'__6 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Relation.Nullary.Decidable.Core.T_Dec_20
d__'8799''8347'__6 v0 v1
  = coe
      MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
      erased (coe (\ v2 -> v2))
      (coe
         MAlonzo.Code.Data.String.Properties.d__'8799'__54 (coe v0)
         (coe v1))
-- Once.TypeCheck.Classify.Imports
d_Imports_14 :: ()
d_Imports_14 = erased
-- Once.TypeCheck.Classify.emptyImports
d_emptyImports_16 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyImports_16
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.PolyCtx
d_PolyCtx_18 :: ()
d_PolyCtx_18 = erased
-- Once.TypeCheck.Classify.emptyPolyCtx
d_emptyPolyCtx_20 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyPolyCtx_20
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.lookupPoly
d_lookupPoly_22 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly_22 v0 v1
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
                                 else coe seq (coe v8) (coe d_lookupPoly_22 (coe v3) (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly
d_removePoly_58 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_removePoly_58 v0 v1
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
                                           (coe d_removePoly_58 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly-decreases
d_removePoly'45'decreases_100 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_removePoly'45'decreases_100 ~v0 v1 v2 ~v3
  = du_removePoly'45'decreases_100 v1 v2
du_removePoly'45'decreases_100 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_removePoly'45'decreases_100 v0 v1
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
                                           (coe du_removePoly'45'decreases_100 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupPolyPrefix
d_lookupPolyPrefix_144 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPolyPrefix_144 v0 v1
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
                                            (coe d_lookupPolyPrefix_144 (coe v3) (coe v1))
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupPolyPrefix-decreases
d_lookupPolyPrefix'45'decreases_190 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_lookupPolyPrefix'45'decreases_190 v0 v1 ~v2 ~v3 v4 ~v5
  = du_lookupPolyPrefix'45'decreases_190 v0 v1 v4
du_lookupPolyPrefix'45'decreases_190 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_lookupPolyPrefix'45'decreases_190 v0 v1 v2
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
                                 then coe seq (coe v9) (coe du_aux_232 (coe v2))
                                 else coe
                                        seq (coe v9)
                                        (coe
                                           du_lookupPolyPrefix'45'decreases_190 (coe v0) (coe v4)
                                           (coe v2))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.aux
d_aux_232 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_aux_232 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11 v12
          ~v13
  = du_aux_232 v12
du_aux_232 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_aux_232 v0
  = coe
      MAlonzo.Code.Data.Nat.Properties.d_'8804''45'refl_2900
      (coe
         addInt (coe (1 :: Integer))
         (coe MAlonzo.Code.Data.List.Base.du_length_268 v0))
-- Once.TypeCheck.Classify.lookupPolyPrefix⇒lookupPoly
d_lookupPolyPrefix'8658'lookupPoly_256 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_lookupPolyPrefix'8658'lookupPoly_256 = erased
-- Once.TypeCheck.Classify._.aux
d_aux_298 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_aux_298 = erased
-- Once.TypeCheck.Classify.lookupPoly⇒lookupPolyPrefix
d_lookupPoly'8658'lookupPolyPrefix_322 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly'8658'lookupPolyPrefix_322 v0 v1 ~v2 ~v3 ~v4
  = du_lookupPoly'8658'lookupPolyPrefix_322 v0 v1
du_lookupPoly'8658'lookupPolyPrefix_322 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_lookupPoly'8658'lookupPolyPrefix_322 v0 v1
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
                                 then coe seq (coe v8) (coe du_aux_364 (coe v3))
                                 else coe
                                        seq (coe v8)
                                        (coe
                                           du_lookupPoly'8658'lookupPolyPrefix_322 (coe v3)
                                           (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.aux
d_aux_364 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_aux_364 ~v0 ~v1 ~v2 ~v3 ~v4 v5 ~v6 ~v7 ~v8 ~v9 ~v10 ~v11
  = du_aux_364 v5
du_aux_364 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_aux_364 v0
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v0) erased
-- Once.TypeCheck.Classify.NamedCtx
d_NamedCtx_378 = ()
data T_NamedCtx_378
  = C_mkCtx_404 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Context.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Classify.NamedCtx.size
d_size_392 :: T_NamedCtx_378 -> Integer
d_size_392 v0
  = case coe v0 of
      C_mkCtx_404 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.named
d_named_394 ::
  T_NamedCtx_378 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_394 v0
  = case coe v0 of
      C_mkCtx_404 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.debruijn
d_debruijn_396 ::
  T_NamedCtx_378 -> MAlonzo.Code.Once.Surface.Context.T_Ctx_6
d_debruijn_396 v0
  = case coe v0 of
      C_mkCtx_404 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.freshCounter
d_freshCounter_398 :: T_NamedCtx_378 -> Integer
d_freshCounter_398 v0
  = case coe v0 of
      C_mkCtx_404 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.imports
d_imports_400 ::
  T_NamedCtx_378 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_400 v0
  = case coe v0 of
      C_mkCtx_404 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.polys
d_polys_402 ::
  T_NamedCtx_378 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_402 v0
  = case coe v0 of
      C_mkCtx_404 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.emptyCtx
d_emptyCtx_406 :: T_NamedCtx_378
d_emptyCtx_406
  = coe
      C_mkCtx_404 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_16)
      (coe d_emptyPolyCtx_20)
-- Once.TypeCheck.Classify.ctxWithImports
d_ctxWithImports_408 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_378
d_ctxWithImports_408 v0
  = coe
      C_mkCtx_404 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe d_emptyPolyCtx_20)
-- Once.TypeCheck.Classify.ctxWithImportsAndPolys
d_ctxWithImportsAndPolys_412 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_378
d_ctxWithImportsAndPolys_412 v0 v1
  = coe
      C_mkCtx_404 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe v1)
-- Once.TypeCheck.Classify.extendNamedCtx
d_extendNamedCtx_418 ::
  T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_378
d_extendNamedCtx_418 v0 v1 v2
  = case coe v0 of
      C_mkCtx_404 v3 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_404 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.bumpFresh
d_bumpFresh_436 :: T_NamedCtx_378 -> T_NamedCtx_378
d_bumpFresh_436 v0
  = case coe v0 of
      C_mkCtx_404 v1 v2 v3 v4 v5 v6
        -> coe
             C_mkCtx_404 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.freshTVar
d_freshTVar_450 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_450 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Classify.lookupImport
d_lookupImport_454 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_lookupImport_454 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupImport_454 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupLocal-go
d_lookupLocal'45'go_496 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'go_496 v0 v1 v2 v3
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
                                               = d_lookupLocal'45'go_496
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
d_lookupLocal_584 ::
  T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_584 v0 v1
  = coe
      d_lookupLocal'45'go_496 (coe d_size_392 (coe v0)) (coe v1)
      (coe d_named_394 (coe v0)) (coe d_debruijn_396 (coe v0))
-- Once.TypeCheck.Classify.LookupLocalView
d_LookupLocalView_594 a0 a1 = ()
data T_LookupLocalView_594
  = C_llv'45'found_606 MAlonzo.Code.Once.Type.T_Type_108
                       MAlonzo.Code.Once.Surface.Context.T_Usage_60
                       MAlonzo.Code.Once.Surface.Context.T_SVar_210 |
    C_llv'45'not'45'found_608
-- Once.TypeCheck.Classify.inspectLookupLocal
d_inspectLookupLocal_614 ::
  T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupLocalView_594
d_inspectLookupLocal_614 v0 v1
  = let v2
          = d_lookupLocal'45'go_496
              (coe d_size_392 (coe v0)) (coe v1) (coe d_named_394 (coe v0))
              (coe d_debruijn_396 (coe v0)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe C_llv'45'found_606 v4 v6 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_llv'45'not'45'found_608
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.LookupImportView
d_LookupImportView_644 a0 a1 = ()
data T_LookupImportView_644
  = C_liv'45'found_652 MAlonzo.Code.Once.Type.T_Type_108 |
    C_liv'45'not'45'found_654
-- Once.TypeCheck.Classify.inspectLookupImport
d_inspectLookupImport_660 ::
  T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupImportView_644
d_inspectLookupImport_660 v0 v1
  = let v2
          = d_lookupImport_454 (coe d_imports_400 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_liv'45'found_652 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_liv'45'not'45'found_654
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.findLocalVarUsage
d_findLocalVarUsage_684 ::
  T_NamedCtx_378 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_684 v0 v1
  = case coe v0 of
      C_mkCtx_404 v2 v3 v4 v5 v6 v7
        -> coe du_go_700 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.go
d_go_700 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_700 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 = du_go_700 v6 v8 v9
du_go_700 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_700 v0 v1 v2
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
                                     (let v12 = coe du_go_700 (coe v0) (coe v4) (coe v6) in
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
d_PolyBuiltinApp_764 = ()
data T_PolyBuiltinApp_764
  = C_pba'45'id_766 | C_pba'45'fst_768 | C_pba'45'snd_770 |
    C_pba'45'terminal_772 | C_pba'45'inl_774 | C_pba'45'inr_776 |
    C_pba'45'initial_778 | C_pba'45'pair'45'applied_780 |
    C_pba'45'compose'45'applied_782 | C_pba'45'case'45'applied_784 |
    C_pba'45'curry_786 | C_pba'45'apply_788 | C_pba'45'In_790 |
    C_pba'45'cata_792 | C_pba'45'ana_794 | C_pba'45'Out_796
-- Once.TypeCheck.Classify.AppHeadView
d_AppHeadView_798 a0 = ()
data T_AppHeadView_798
  = C_ahv'45'id_800 | C_ahv'45'fst_802 | C_ahv'45'snd_804 |
    C_ahv'45'terminal_806 | C_ahv'45'inl_808 | C_ahv'45'inr_810 |
    C_ahv'45'initial_812 | C_ahv'45'curry_814 | C_ahv'45'apply_816 |
    C_ahv'45'In_818 | C_ahv'45'cata_820 | C_ahv'45'ana_822 |
    C_ahv'45'Out_824 | C_ahv'45'pair'45'applied_828 |
    C_ahv'45'compose'45'applied_832 | C_ahv'45'case'45'applied_836 |
    C_ahv'45'other_840
-- Once.TypeCheck.Classify.classifyAppHeadView
d_classifyAppHeadView_844 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_798
d_classifyAppHeadView_844 v0
  = case coe v0 of
      MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v1
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v1
        -> case coe v1 of
             MAlonzo.Code.Once.CanonicalName.C_canonical_10 v2
               -> case coe v2 of
                    [] -> coe C_ahv'45'other_840
                    (:) v3 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_840
                           (:) v5 v6
                             -> case coe v6 of
                                  []
                                    -> let v7
                                             = coe
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                 erased (coe (\ v7 -> v7))
                                                 (coe
                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                     erased (coe (\ v10 -> v10))
                                                                     (coe
                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                              (coe C_ahv'45'id_800)
                                                                       else coe
                                                                              seq (coe v12)
                                                                              (let v13
                                                                                     = coe
                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                         erased
                                                                                         (coe
                                                                                            (\ v13 ->
                                                                                               v13))
                                                                                         (coe
                                                                                            MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                     C_ahv'45'fst_802)
                                                                                           else coe
                                                                                                  seq
                                                                                                  (coe
                                                                                                     v15)
                                                                                                  (let v16
                                                                                                         = coe
                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                             erased
                                                                                                             (coe
                                                                                                                (\ v16 ->
                                                                                                                   v16))
                                                                                                             (coe
                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                         C_ahv'45'snd_804)
                                                                                                               else coe
                                                                                                                      seq
                                                                                                                      (coe
                                                                                                                         v18)
                                                                                                                      (let v19
                                                                                                                             = coe
                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                 erased
                                                                                                                                 (coe
                                                                                                                                    (\ v19 ->
                                                                                                                                       v19))
                                                                                                                                 (coe
                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                             C_ahv'45'terminal_806)
                                                                                                                                   else coe
                                                                                                                                          seq
                                                                                                                                          (coe
                                                                                                                                             v21)
                                                                                                                                          (let v22
                                                                                                                                                 = coe
                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                     erased
                                                                                                                                                     (coe
                                                                                                                                                        (\ v22 ->
                                                                                                                                                           v22))
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                                                 C_ahv'45'inl_808)
                                                                                                                                                       else coe
                                                                                                                                                              seq
                                                                                                                                                              (coe
                                                                                                                                                                 v24)
                                                                                                                                                              (let v25
                                                                                                                                                                     = coe
                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                         erased
                                                                                                                                                                         (coe
                                                                                                                                                                            (\ v25 ->
                                                                                                                                                                               v25))
                                                                                                                                                                         (coe
                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                                                                     C_ahv'45'inr_810)
                                                                                                                                                                           else coe
                                                                                                                                                                                  seq
                                                                                                                                                                                  (coe
                                                                                                                                                                                     v27)
                                                                                                                                                                                  (let v28
                                                                                                                                                                                         = coe
                                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                             erased
                                                                                                                                                                                             (coe
                                                                                                                                                                                                (\ v28 ->
                                                                                                                                                                                                   v28))
                                                                                                                                                                                             (coe
                                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                                                                                         C_ahv'45'initial_812)
                                                                                                                                                                                               else coe
                                                                                                                                                                                                      seq
                                                                                                                                                                                                      (coe
                                                                                                                                                                                                         v30)
                                                                                                                                                                                                      (let v31
                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                 erased
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    (\ v31 ->
                                                                                                                                                                                                                       v31))
                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                                                                                                             C_ahv'45'curry_814)
                                                                                                                                                                                                                   else coe
                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                             v33)
                                                                                                                                                                                                                          (let v34
                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                     erased
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        (\ v34 ->
                                                                                                                                                                                                                                           v34))
                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                                                                                                                                 C_ahv'45'apply_816)
                                                                                                                                                                                                                                       else coe
                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                 v36)
                                                                                                                                                                                                                                              (let v37
                                                                                                                                                                                                                                                     = coe
                                                                                                                                                                                                                                                         MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                         erased
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            (\ v37 ->
                                                                                                                                                                                                                                                               v37))
                                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                                            MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                                                                                                                                                     C_ahv'45'In_818)
                                                                                                                                                                                                                                                           else coe
                                                                                                                                                                                                                                                                  seq
                                                                                                                                                                                                                                                                  (coe
                                                                                                                                                                                                                                                                     v39)
                                                                                                                                                                                                                                                                  (let v40
                                                                                                                                                                                                                                                                         = coe
                                                                                                                                                                                                                                                                             MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                                             erased
                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                (\ v40 ->
                                                                                                                                                                                                                                                                                   v40))
                                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                                MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                                                                                                                                                                                                                         C_ahv'45'cata_820)
                                                                                                                                                                                                                                                                               else coe
                                                                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                                                                         v42)
                                                                                                                                                                                                                                                                                      (let v43
                                                                                                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                                                                 erased
                                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                                    (\ v43 ->
                                                                                                                                                                                                                                                                                                       v43))
                                                                                                                                                                                                                                                                                                 (coe
                                                                                                                                                                                                                                                                                                    MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                                       v5)
                                                                                                                                                                                                                                                                                                    (coe
                                                                                                                                                                                                                                                                                                       ("ana"
                                                                                                                                                                                                                                                                                                        ::
                                                                                                                                                                                                                                                                                                        Data.Text.Text))) in
                                                                                                                                                                                                                                                                                       coe
                                                                                                                                                                                                                                                                                         (case coe
                                                                                                                                                                                                                                                                                                 v43 of
                                                                                                                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v44 v45
                                                                                                                                                                                                                                                                                              -> if coe
                                                                                                                                                                                                                                                                                                      v44
                                                                                                                                                                                                                                                                                                   then coe
                                                                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                                             v45)
                                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                                             C_ahv'45'ana_822)
                                                                                                                                                                                                                                                                                                   else coe
                                                                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                                                                             v45)
                                                                                                                                                                                                                                                                                                          (let v46
                                                                                                                                                                                                                                                                                                                 = coe
                                                                                                                                                                                                                                                                                                                     MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                                                                                     erased
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        (\ v46 ->
                                                                                                                                                                                                                                                                                                                           v46))
                                                                                                                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                                                                                                                        MAlonzo.Code.Data.String.Properties.d__'8799'__54
                                                                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                                                                           v5)
                                                                                                                                                                                                                                                                                                                        (coe
                                                                                                                                                                                                                                                                                                                           ("Out"
                                                                                                                                                                                                                                                                                                                            ::
                                                                                                                                                                                                                                                                                                                            Data.Text.Text))) in
                                                                                                                                                                                                                                                                                                           coe
                                                                                                                                                                                                                                                                                                             (case coe
                                                                                                                                                                                                                                                                                                                     v46 of
                                                                                                                                                                                                                                                                                                                MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v47 v48
                                                                                                                                                                                                                                                                                                                  -> if coe
                                                                                                                                                                                                                                                                                                                          v47
                                                                                                                                                                                                                                                                                                                       then coe
                                                                                                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 v48)
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 C_ahv'45'Out_824)
                                                                                                                                                                                                                                                                                                                       else coe
                                                                                                                                                                                                                                                                                                                              seq
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 v48)
                                                                                                                                                                                                                                                                                                                              (coe
                                                                                                                                                                                                                                                                                                                                 C_ahv'45'other_840)
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
                                                                                    _ -> MAlonzo.RTE.mazUnreachableError))
                                                                _ -> MAlonzo.RTE.mazUnreachableError))
                                                   else coe seq (coe v9) (coe C_ahv'45'other_840)
                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                  (:) v7 v8 -> coe C_ahv'45'other_840
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v1 v2
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v3
               -> case coe v3 of
                    MAlonzo.Code.Once.CanonicalName.C_canonical_10 v4
                      -> case coe v4 of
                           [] -> coe C_ahv'45'other_840
                           (:) v5 v6
                             -> case coe v6 of
                                  [] -> coe C_ahv'45'other_840
                                  (:) v7 v8
                                    -> case coe v8 of
                                         []
                                           -> let v9
                                                    = coe
                                                        MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                        erased (coe (\ v9 -> v9))
                                                        (coe
                                                           MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                            (coe (\ v12 -> v12))
                                                                            (coe
                                                                               MAlonzo.Code.Data.String.Properties.d__'8799'__54
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
                                                                                        C_ahv'45'pair'45'applied_828)
                                                                              else coe
                                                                                     seq (coe v14)
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
                                                                                                            C_ahv'45'compose'45'applied_832)
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
                                                                                                                                C_ahv'45'case'45'applied_836)
                                                                                                                      else coe
                                                                                                                             seq
                                                                                                                             (coe
                                                                                                                                v20)
                                                                                                                             (coe
                                                                                                                                C_ahv'45'other_840)
                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                           _ -> MAlonzo.RTE.mazUnreachableError))
                                                                       _ -> MAlonzo.RTE.mazUnreachableError))
                                                          else coe
                                                                 seq (coe v11)
                                                                 (coe C_ahv'45'other_840)
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         (:) v9 v10 -> coe C_ahv'45'other_840
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v3 v4
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v3 v4
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v3 v4 v5
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v3 v4
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v3
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v3 v4 v5 v6
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v3
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v3 v4
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v3 v4 v5
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v4
               -> coe C_ahv'45'other_840
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v3 v4
               -> coe C_ahv'45'other_840
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v1 v2
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v1 v2 v3
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v1 v2
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v1
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RFloat_56 v1 v2 v3 v4
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v1
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v1 v2
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v1 v2 v3
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v2
        -> coe C_ahv'45'other_840
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_66 v1 v2
        -> coe C_ahv'45'other_840
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.viewToPba
d_viewToPba_1072 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_AppHeadView_798 -> Maybe T_PolyBuiltinApp_764
d_viewToPba_1072 ~v0 v1 = du_viewToPba_1072 v1
du_viewToPba_1072 ::
  T_AppHeadView_798 -> Maybe T_PolyBuiltinApp_764
du_viewToPba_1072 v0
  = case coe v0 of
      C_ahv'45'id_800
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_766)
      C_ahv'45'fst_802
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'fst_768)
      C_ahv'45'snd_804
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'snd_770)
      C_ahv'45'terminal_806
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'terminal_772)
      C_ahv'45'inl_808
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inl_774)
      C_ahv'45'inr_810
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inr_776)
      C_ahv'45'initial_812
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'initial_778)
      C_ahv'45'curry_814
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'curry_786)
      C_ahv'45'apply_816
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'apply_788)
      C_ahv'45'In_818
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'In_790)
      C_ahv'45'cata_820
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'cata_792)
      C_ahv'45'ana_822
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'ana_794)
      C_ahv'45'Out_824
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'Out_796)
      C_ahv'45'pair'45'applied_828
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'pair'45'applied_780)
      C_ahv'45'compose'45'applied_832
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'compose'45'applied_782)
      C_ahv'45'case'45'applied_836
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'case'45'applied_784)
      C_ahv'45'other_840
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.classifyAppHead
d_classifyAppHead_1074 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_764
d_classifyAppHead_1074 v0
  = coe du_viewToPba_1072 (coe d_classifyAppHeadView_844 (coe v0))
-- Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_1080 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_1080 = erased
-- Once.TypeCheck.Classify.view-other⇒classifyAppHead-nothing
d_view'45'other'8658'classifyAppHead'45'nothing_1160 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_view'45'other'8658'classifyAppHead'45'nothing_1160 = erased
-- Once.TypeCheck.Classify.GenView
d_GenView_1170 a0 = ()
data T_GenView_1170
  = C_gv'45'id_1172 | C_gv'45'fst_1174 | C_gv'45'snd_1176 |
    C_gv'45'terminal_1178 | C_gv'45'initial_1180 | C_gv'45'inl_1182 |
    C_gv'45'inr_1184 | C_gv'45'unit_1186 |
    C_gv'45'other_1190 MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
-- Once.TypeCheck.Classify.notGen-ns
d_notGen'45'ns_1196 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_notGen'45'ns_1196 ~v0 ~v1 ~v2 = du_notGen'45'ns_1196
du_notGen'45'ns_1196 ::
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_notGen'45'ns_1196
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
d_f_1210 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  (MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_f_1210 = erased
-- Once.TypeCheck.Classify.notGen-shape
d_notGen'45'shape_1216 ::
  [MAlonzo.Code.Agda.Builtin.String.T_String_6] ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
d_notGen'45'shape_1216 ~v0 v1 = du_notGen'45'shape_1216 v1
du_notGen'45'shape_1216 ::
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
   MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.List.Relation.Unary.All.T_All_44
du_notGen'45'shape_1216 v0
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
d_classifyGen_1222 ::
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 -> T_GenView_1170
d_classifyGen_1222 v0
  = case coe v0 of
      MAlonzo.Code.Once.CanonicalName.C_canonical_10 v1
        -> case coe v1 of
             [] -> coe C_gv'45'other_1190 (coe du_notGen'45'shape_1216 erased)
             (:) v2 v3
               -> case coe v3 of
                    [] -> coe C_gv'45'other_1190 (coe du_notGen'45'shape_1216 erased)
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
                                                                       (coe C_gv'45'id_1172)
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
                                                                                              C_gv'45'fst_1174)
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
                                                                                                                  C_gv'45'snd_1176)
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
                                                                                                                                      C_gv'45'terminal_1178)
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
                                                                                                                                                          C_gv'45'initial_1180)
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
                                                                                                                                                                              C_gv'45'inl_1182)
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
                                                                                                                                                                                                  C_gv'45'inr_1184)
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
                                                                                                                                                                                                                      C_gv'45'unit_1186)
                                                                                                                                                                                                            else coe
                                                                                                                                                                                                                   seq
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      v32)
                                                                                                                                                                                                                   (coe
                                                                                                                                                                                                                      C_gv'45'other_1190
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
                                                      C_gv'45'other_1190 (coe du_notGen'45'ns_1196))
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           (:) v6 v7
                             -> coe C_gv'45'other_1190 (coe du_notGen'45'shape_1216 erased)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.ViewBundle
d_ViewBundle_1482 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_ViewBundle_1482 = erased
-- Once.TypeCheck.Classify.viewBundle
d_viewBundle_1490 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_1490 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_classifyAppHeadView_844 (coe v0)) erased
