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
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Surface.Thinning
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
-- Once.TypeCheck.Classify.NamedCtx
d_NamedCtx_170 = ()
data T_NamedCtx_170
  = C_mkCtx_200 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Classify.NamedCtx.size
d_size_186 :: T_NamedCtx_170 -> Integer
d_size_186 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.named
d_named_188 ::
  T_NamedCtx_170 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_188 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.debruijn
d_debruijn_190 ::
  T_NamedCtx_170 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_190 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.freshCounter
d_freshCounter_192 :: T_NamedCtx_170 -> Integer
d_freshCounter_192 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.imports
d_imports_194 ::
  T_NamedCtx_170 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_194 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.polys
d_polys_196 ::
  T_NamedCtx_170 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_196 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.sigEffects
d_sigEffects_198 ::
  T_NamedCtx_170 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_sigEffects_198 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7 -> coe v7
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.emptyCtx
d_emptyCtx_202 :: T_NamedCtx_170
d_emptyCtx_202
  = coe
      C_mkCtx_200 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_8) (coe d_emptyPolyCtx_46)
      (coe d_emptySigEffects_12)
-- Once.TypeCheck.Classify.ctxWithImports
d_ctxWithImports_204 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_170
d_ctxWithImports_204 v0
  = coe
      C_mkCtx_200 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe d_emptyPolyCtx_46)
      (coe d_emptySigEffects_12)
-- Once.TypeCheck.Classify.ctxWithImportsAndPolys
d_ctxWithImportsAndPolys_208 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_170
d_ctxWithImportsAndPolys_208 v0 v1
  = coe
      C_mkCtx_200 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe v1) (coe d_emptySigEffects_12)
-- Once.TypeCheck.Classify.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_214 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> T_NamedCtx_170
d_ctxWithImportsAndSelf_214 v0 v1 v2
  = coe
      d_ctxWithImports_204
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Classify.ctxWithImportsAndSelfAndPolys
d_ctxWithImportsAndSelfAndPolys_222 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> T_NamedCtx_170
d_ctxWithImportsAndSelfAndPolys_222 v0 v1 v2 v3 v4
  = coe
      C_mkCtx_200 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer))
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v4))
         (coe v0))
      (coe v1) (coe v2)
-- Once.TypeCheck.Classify.extendNamedCtx
d_extendNamedCtx_234 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> T_NamedCtx_170
d_extendNamedCtx_234 v0 v1 v2
  = case coe v0 of
      C_mkCtx_200 v3 v4 v5 v6 v7 v8 v9
        -> coe
             C_mkCtx_200 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7) (coe v8) (coe v9)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.bumpFresh
d_bumpFresh_254 :: T_NamedCtx_170 -> T_NamedCtx_170
d_bumpFresh_254 v0
  = case coe v0 of
      C_mkCtx_200 v1 v2 v3 v4 v5 v6 v7
        -> coe
             C_mkCtx_200 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5) (coe v6)
             (coe v7)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.freshTVar
d_freshTVar_270 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_270 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Classify.lookupImport
d_lookupImport_274 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_lookupImport_274 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupImport_274 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupLocal-go
d_lookupLocal'45'go_316 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'go_316 v0 v1 v2 v3
  = case coe v2 of
      []
        -> coe
             seq (coe v3) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v4 v5
        -> case coe v3 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v7 v8 v9
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
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v8)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.d_singleUse_76
                                                    (coe v0)
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                    (coe MAlonzo.Code.Once.Type.C_One_8))
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.C_var_192
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                 else coe
                                        seq (coe v13)
                                        (let v14
                                               = d_lookupLocal'45'go_316
                                                   (coe v10) (coe v1) (coe v5) (coe v7) in
                                         coe
                                           (case coe v14 of
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                                                -> case coe v15 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                                       -> case coe v17 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                                              -> coe
                                                                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v16)
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__66
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Zero_6)
                                                                            v18)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Thinning.du_weaken_958
                                                                            (coe v7) (coe v8)
                                                                            (coe v16) (coe v9)
                                                                            (coe v19))))
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                              MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                                -> coe v14
                                              _ -> MAlonzo.RTE.mazUnreachableError))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupLocal
d_lookupLocal_404 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_404 v0 v1
  = coe
      d_lookupLocal'45'go_316 (coe d_size_186 (coe v0)) (coe v1)
      (coe d_named_188 (coe v0)) (coe d_debruijn_190 (coe v0))
-- Once.TypeCheck.Classify.LookupLocalView
d_LookupLocalView_414 a0 a1 = ()
data T_LookupLocalView_414
  = C_llv'45'found_426 MAlonzo.Code.Once.Type.T_Type_112
                       MAlonzo.Code.Once.Surface.Syntax.T_Usage_60
                       MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 |
    C_llv'45'not'45'found_428
-- Once.TypeCheck.Classify.inspectLookupLocal
d_inspectLookupLocal_434 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupLocalView_414
d_inspectLookupLocal_434 v0 v1
  = let v2
          = d_lookupLocal'45'go_316
              (coe d_size_186 (coe v0)) (coe v1) (coe d_named_188 (coe v0))
              (coe d_debruijn_190 (coe v0)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe C_llv'45'found_426 v4 v6 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_llv'45'not'45'found_428
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.LookupImportView
d_LookupImportView_464 a0 a1 = ()
data T_LookupImportView_464
  = C_liv'45'found_472 MAlonzo.Code.Once.Type.T_Type_112 |
    C_liv'45'not'45'found_474
-- Once.TypeCheck.Classify.inspectLookupImport
d_inspectLookupImport_480 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupImportView_464
d_inspectLookupImport_480 v0 v1
  = let v2
          = d_lookupImport_274 (coe d_imports_194 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_liv'45'found_472 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_liv'45'not'45'found_474
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.composeArgB-lookup
d_composeArgB'45'lookup_502 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_composeArgB'45'lookup_502 v0 v1 v2
  = let v3 = d_lookupPoly_48 (coe d_polys_196 (coe v0)) (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v4
           -> case coe v4 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
                  -> coe
                       MAlonzo.Code.Once.Type.d_schemaArrowCodomain_860 (coe v5) (coe v2)
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> let v4
                    = d_lookupImport_274 (coe d_imports_194 (coe v0)) (coe v1) in
              coe
                (case coe v4 of
                   MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v5
                     -> case coe v5 of
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v6 v7 v8
                            -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v8)
                          _ -> coe v3
                   _ -> coe v3)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.composeArgB-fst
d_composeArgB'45'fst_546 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_composeArgB'45'fst_546 v0 v1
  = let v2
          = d_composeArgB'45'lookup_502
              (coe v0) (coe ("fst" :: Data.Text.Text)) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C__'42'__126 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
         _ -> coe v2)
-- Once.TypeCheck.Classify.composeArgB-snd
d_composeArgB'45'snd_556 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_composeArgB'45'snd_556 v0 v1
  = let v2
          = d_composeArgB'45'lookup_502
              (coe v0) (coe ("snd" :: Data.Text.Text)) (coe v1) in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.Type.C__'42'__126 v3 v4
           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v4)
         _ -> coe v2)
-- Once.TypeCheck.Classify.composeArgB-rvar
d_composeArgB'45'rvar_566 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_composeArgB'45'rvar_566 v0 v1 v2
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
                       seq (coe v5) (coe d_composeArgB'45'fst_546 (coe v0) (coe v2))
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
                                           (coe d_composeArgB'45'snd_556 (coe v0) (coe v2))
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
                                                                                         MAlonzo.Code.Once.Type.C_Unit_122))
                                                                            else coe
                                                                                   seq (coe v14)
                                                                                   (coe
                                                                                      d_composeArgB'45'lookup_502
                                                                                      (coe v0)
                                                                                      (coe v1)
                                                                                      (coe v2))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.composeArgB
d_composeArgB_638 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_composeArgB_638 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> coe d_composeArgB'45'rvar_566 (coe v0) (coe v4) (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v4
           -> coe
                d_composeArgB'45'lookup_502 (coe v0)
                (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v4))
                (coe v2)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v8
                         -> case coe v8 of
                              l | (==) l ("compose" :: Data.Text.Text) ->
                                  let v9 = d_composeArgB_638 (coe v0) (coe v5) (coe v2) in
                                  coe
                                    (case coe v9 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                         -> coe d_composeArgB_638 (coe v0) (coe v7) (coe v10)
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3
         MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v4
           -> coe
                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                (coe MAlonzo.Code.Once.Type.C_Int_136)
         _ -> coe v3)
-- Once.TypeCheck.Classify.domainOfHead-arrow
d_domainOfHead'45'arrow_710 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_domainOfHead'45'arrow_710 v0
  = let v1 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v0 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2
           -> case coe v2 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v3 v4 v5
                  -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v3)
                _ -> coe v1
         _ -> coe v1)
-- Once.TypeCheck.Classify.domainOfHead
d_domainOfHead_714 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_domainOfHead_714 v0 v1
  = let v2 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v3
           -> coe
                d_domainOfHead'45'arrow_710
                (coe d_lookupImport_274 (coe d_imports_194 (coe v0)) (coe v3))
         MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v3
           -> coe
                d_domainOfHead'45'arrow_710
                (coe
                   d_lookupImport_274 (coe d_imports_194 (coe v0))
                   (coe MAlonzo.Code.Once.CanonicalName.d_showCanonical_40 (coe v3)))
         _ -> coe v2)
-- Once.TypeCheck.Classify.composeMid-pick
d_composeMid'45'pick_724 ::
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_composeMid'45'pick_724 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v2 -> coe v0
      MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.composeMid
d_composeMid_730 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112
d_composeMid_730 v0 v1 v2 v3
  = coe
      d_composeMid'45'pick_724
      (coe d_composeArgB_638 (coe v0) (coe v2) (coe v3))
      (coe d_domainOfHead_714 (coe v0) (coe v1))
-- Once.TypeCheck.Classify.findLocalVarUsage
d_findLocalVarUsage_742 ::
  T_NamedCtx_170 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_742 v0 v1
  = case coe v0 of
      C_mkCtx_200 v2 v3 v4 v5 v6 v7 v8
        -> coe du_go_758 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.go
d_go_758 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_758 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 v7 ~v8 v9 v10
  = du_go_758 v7 v9 v10
du_go_758 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_758 v0 v1 v2
  = case coe v1 of
      []
        -> coe
             seq (coe v2) (coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
      (:) v3 v4
        -> case coe v2 of
             MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v6 v7 v8
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
                                     (let v12 = coe du_go_758 (coe v0) (coe v4) (coe v6) in
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
d_PolyBuiltinApp_822 = ()
data T_PolyBuiltinApp_822
  = C_pba'45'id_824 | C_pba'45'fst_826 | C_pba'45'snd_828 |
    C_pba'45'terminal_830 | C_pba'45'inl_832 | C_pba'45'inr_834 |
    C_pba'45'initial_836 | C_pba'45'pair'45'applied_838 |
    C_pba'45'compose'45'applied_840 | C_pba'45'case'45'applied_842 |
    C_pba'45'curry_844 | C_pba'45'apply_846 | C_pba'45'In_848 |
    C_pba'45'cata_850
-- Once.TypeCheck.Classify.AppHeadView
d_AppHeadView_852 a0 = ()
data T_AppHeadView_852
  = C_ahv'45'id_854 | C_ahv'45'fst_856 | C_ahv'45'snd_858 |
    C_ahv'45'terminal_860 | C_ahv'45'inl_862 | C_ahv'45'inr_864 |
    C_ahv'45'initial_866 | C_ahv'45'curry_868 | C_ahv'45'apply_870 |
    C_ahv'45'In_872 | C_ahv'45'cata_874 |
    C_ahv'45'pair'45'applied_878 | C_ahv'45'compose'45'applied_882 |
    C_ahv'45'case'45'applied_886 | C_ahv'45'other_890
-- Once.TypeCheck.Classify.classifyAppHeadView
d_classifyAppHeadView_894 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_852
d_classifyAppHeadView_894 v0
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
                       then coe seq (coe v4) (coe C_ahv'45'id_854)
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
                                           then coe seq (coe v7) (coe C_ahv'45'fst_856)
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
                                                                      (coe C_ahv'45'snd_858)
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
                                                                                             C_ahv'45'terminal_860)
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
                                                                                                                 C_ahv'45'inl_862)
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
                                                                                                                                     C_ahv'45'inr_864)
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
                                                                                                                                                         C_ahv'45'initial_866)
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
                                                                                                                                                                             C_ahv'45'curry_868)
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
                                                                                                                                                                                                 C_ahv'45'apply_870)
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
                                                                                                                                                                                                                     C_ahv'45'In_872)
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
                                                                                                                                                                                                                                         C_ahv'45'cata_874)
                                                                                                                                                                                                                               else coe
                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v34)
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         C_ahv'45'other_890)
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
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v1
        -> coe C_ahv'45'other_890
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
                              then coe seq (coe v6) (coe C_ahv'45'pair'45'applied_878)
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
                                                         (coe C_ahv'45'compose'45'applied_882)
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
                                                                                C_ahv'45'case'45'applied_886)
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                C_ahv'45'other_890)
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v3
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v3 v4
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v3 v4
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v3 v4 v5
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v3 v4
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v3
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_56 v3
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v3 v4
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v3 v4 v5
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v4
               -> coe C_ahv'45'other_890
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_64 v3 v4
               -> coe C_ahv'45'other_890
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v1 v2
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v1 v2 v3
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v1 v2
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_52
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v1
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_56 v1
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_58 v1 v2
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_60 v1 v2 v3
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_62 v2
        -> coe C_ahv'45'other_890
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAna_64 v1 v2
        -> coe C_ahv'45'other_890
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.viewToPba
d_viewToPba_1014 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  T_AppHeadView_852 -> Maybe T_PolyBuiltinApp_822
d_viewToPba_1014 ~v0 v1 = du_viewToPba_1014 v1
du_viewToPba_1014 ::
  T_AppHeadView_852 -> Maybe T_PolyBuiltinApp_822
du_viewToPba_1014 v0
  = case coe v0 of
      C_ahv'45'id_854
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_824)
      C_ahv'45'fst_856
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'fst_826)
      C_ahv'45'snd_858
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'snd_828)
      C_ahv'45'terminal_860
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'terminal_830)
      C_ahv'45'inl_862
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inl_832)
      C_ahv'45'inr_864
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'inr_834)
      C_ahv'45'initial_866
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'initial_836)
      C_ahv'45'curry_868
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'curry_844)
      C_ahv'45'apply_870
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'apply_846)
      C_ahv'45'In_872
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'In_848)
      C_ahv'45'cata_874
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'cata_850)
      C_ahv'45'pair'45'applied_878
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'pair'45'applied_838)
      C_ahv'45'compose'45'applied_882
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'compose'45'applied_840)
      C_ahv'45'case'45'applied_886
        -> coe
             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
             (coe C_pba'45'case'45'applied_842)
      C_ahv'45'other_890
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.classifyAppHead
d_classifyAppHead_1016 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_822
d_classifyAppHead_1016 v0
  = coe du_viewToPba_1014 (coe d_classifyAppHeadView_894 (coe v0))
-- Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_1022 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_1022 = erased
-- Once.TypeCheck.Classify.view-other⇒classifyAppHead-nothing
d_view'45'other'8658'classifyAppHead'45'nothing_1094 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_view'45'other'8658'classifyAppHead'45'nothing_1094 = erased
-- Once.TypeCheck.Classify.BareBuiltinClass
d_BareBuiltinClass_1104 a0 = ()
data T_BareBuiltinClass_1104
  = C_bbc'45'id_1106 | C_bbc'45'fst_1108 | C_bbc'45'snd_1110 |
    C_bbc'45'terminal_1112 | C_bbc'45'initial_1114 |
    C_bbc'45'inl_1116 | C_bbc'45'inr_1118 | C_bbc'45'other_1122
-- Once.TypeCheck.Classify.classifyBareBuiltin
d_classifyBareBuiltin_1126 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_BareBuiltinClass_1104
d_classifyBareBuiltin_1126 v0
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
                then coe seq (coe v3) (coe C_bbc'45'id_1106)
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
                                    then coe seq (coe v6) (coe C_bbc'45'fst_1108)
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
                                                               seq (coe v9) (coe C_bbc'45'snd_1110)
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
                                                                                      C_bbc'45'terminal_1112)
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
                                                                                                          C_bbc'45'initial_1114)
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
                                                                                                                              C_bbc'45'inl_1116)
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
                                                                                                                                                  C_bbc'45'inr_1118)
                                                                                                                                        else coe
                                                                                                                                               seq
                                                                                                                                               (coe
                                                                                                                                                  v21)
                                                                                                                                               (coe
                                                                                                                                                  C_bbc'45'other_1122)
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.ViewBundle
d_ViewBundle_1186 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_ViewBundle_1186 = erased
-- Once.TypeCheck.Classify.viewBundle
d_viewBundle_1194 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_1194 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_classifyAppHeadView_894 (coe v0)) erased
