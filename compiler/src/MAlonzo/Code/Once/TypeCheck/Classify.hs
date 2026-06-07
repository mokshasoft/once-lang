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
-- Once.TypeCheck.Classify.PolyCtx
d_PolyCtx_10 :: ()
d_PolyCtx_10 = erased
-- Once.TypeCheck.Classify.emptyPolyCtx
d_emptyPolyCtx_12 :: [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_emptyPolyCtx_12
  = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
-- Once.TypeCheck.Classify.lookupPoly
d_lookupPoly_14 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupPoly_14 v0 v1
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
                                 else coe seq (coe v8) (coe d_lookupPoly_14 (coe v3) (coe v1))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly
d_removePoly_50 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_removePoly_50 v0 v1
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
                                           (coe d_removePoly_50 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.removePoly-decreases
d_removePoly'45'decreases_92 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
d_removePoly'45'decreases_92 ~v0 v1 v2 ~v3
  = du_removePoly'45'decreases_92 v1 v2
du_removePoly'45'decreases_92 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Data.Nat.Base.T__'8804'__22
du_removePoly'45'decreases_92 v0 v1
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
                                           (coe du_removePoly'45'decreases_92 (coe v0) (coe v3)))
                          _ -> MAlonzo.RTE.mazUnreachableError))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx
d_NamedCtx_136 = ()
data T_NamedCtx_136
  = C_mkCtx_162 Integer
                [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
                MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 Integer
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
                [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
-- Once.TypeCheck.Classify.NamedCtx.size
d_size_150 :: T_NamedCtx_136 -> Integer
d_size_150 v0
  = case coe v0 of
      C_mkCtx_162 v1 v2 v3 v4 v5 v6 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.named
d_named_152 ::
  T_NamedCtx_136 -> [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6]
d_named_152 v0
  = case coe v0 of
      C_mkCtx_162 v1 v2 v3 v4 v5 v6 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.debruijn
d_debruijn_154 ::
  T_NamedCtx_136 -> MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6
d_debruijn_154 v0
  = case coe v0 of
      C_mkCtx_162 v1 v2 v3 v4 v5 v6 -> coe v3
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.freshCounter
d_freshCounter_156 :: T_NamedCtx_136 -> Integer
d_freshCounter_156 v0
  = case coe v0 of
      C_mkCtx_162 v1 v2 v3 v4 v5 v6 -> coe v4
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.imports
d_imports_158 ::
  T_NamedCtx_136 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_imports_158 v0
  = case coe v0 of
      C_mkCtx_162 v1 v2 v3 v4 v5 v6 -> coe v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.NamedCtx.polys
d_polys_160 ::
  T_NamedCtx_136 -> [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14]
d_polys_160 v0
  = case coe v0 of
      C_mkCtx_162 v1 v2 v3 v4 v5 v6 -> coe v6
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.emptyCtx
d_emptyCtx_164 :: T_NamedCtx_136
d_emptyCtx_164
  = coe
      C_mkCtx_162 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe d_emptyImports_8) (coe d_emptyPolyCtx_12)
-- Once.TypeCheck.Classify.ctxWithImports
d_ctxWithImports_166 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_136
d_ctxWithImports_166 v0
  = coe
      C_mkCtx_162 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe d_emptyPolyCtx_12)
-- Once.TypeCheck.Classify.ctxWithImportsAndPolys
d_ctxWithImportsAndPolys_170 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] -> T_NamedCtx_136
d_ctxWithImportsAndPolys_170 v0 v1
  = coe
      C_mkCtx_162 (coe (0 :: Integer))
      (coe MAlonzo.Code.Once.TypeCheck.Context.d_'8709'_24)
      (coe MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
      (coe (0 :: Integer)) (coe v0) (coe v1)
-- Once.TypeCheck.Classify.ctxWithImportsAndSelf
d_ctxWithImportsAndSelf_176 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_136
d_ctxWithImportsAndSelf_176 v0 v1 v2
  = coe
      d_ctxWithImports_166
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v1) (coe v2))
         (coe v0))
-- Once.TypeCheck.Classify.ctxWithImportsAndSelfAndPolys
d_ctxWithImportsAndSelfAndPolys_184 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_136
d_ctxWithImportsAndSelfAndPolys_184 v0 v1 v2 v3
  = coe
      d_ctxWithImportsAndPolys_170
      (coe
         MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v2) (coe v3))
         (coe v0))
      (coe v1)
-- Once.TypeCheck.Classify.extendNamedCtx
d_extendNamedCtx_194 ::
  T_NamedCtx_136 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 -> T_NamedCtx_136
d_extendNamedCtx_194 v0 v1 v2
  = case coe v0 of
      C_mkCtx_162 v3 v4 v5 v6 v7 v8
        -> coe
             C_mkCtx_162 (coe addInt (coe (1 :: Integer)) (coe v3))
             (coe
                MAlonzo.Code.Once.TypeCheck.Context.d__'44'_'8759'__26 (coe v4)
                (coe v1) (coe v2))
             (coe
                MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v5) (coe v2))
             (coe v6) (coe v7) (coe v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.bumpFresh
d_bumpFresh_212 :: T_NamedCtx_136 -> T_NamedCtx_136
d_bumpFresh_212 v0
  = case coe v0 of
      C_mkCtx_162 v1 v2 v3 v4 v5 v6
        -> coe
             C_mkCtx_162 (coe v1) (coe v2) (coe v3)
             (coe addInt (coe (1 :: Integer)) (coe v4)) (coe v5) (coe v6)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.freshTVar
d_freshTVar_226 ::
  Integer -> MAlonzo.Code.Agda.Builtin.String.T_String_6
d_freshTVar_226 v0
  = coe
      MAlonzo.Code.Data.String.Base.d__'43''43'__20
      ("\945" :: Data.Text.Text)
      (coe MAlonzo.Code.Data.Nat.Show.d_show_56 v0)
-- Once.TypeCheck.Classify.lookupImport
d_lookupImport_230 ::
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_lookupImport_230 v0 v1
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
                              else coe seq (coe v8) (coe d_lookupImport_230 (coe v3) (coe v1))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.lookupLocal-go
d_lookupLocal'45'go_272 ::
  Integer ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal'45'go_272 v0 v1 v2 v3
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
                                                    MAlonzo.Code.Once.Surface.Syntax.d_singleUse_66
                                                    (coe v0)
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)
                                                    (coe MAlonzo.Code.Once.Type.C_One_8))
                                                 (coe
                                                    MAlonzo.Code.Once.Surface.Syntax.C_var_182
                                                    (coe MAlonzo.Code.Data.Fin.Base.C_zero_12)))))
                                 else coe
                                        seq (coe v13)
                                        (let v14
                                               = d_lookupLocal'45'go_272
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
                                                                            MAlonzo.Code.Once.Surface.Syntax.C__'8759'__56
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_Zero_6)
                                                                            v18)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Thinning.du_weaken_948
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
d_lookupLocal_360 ::
  T_NamedCtx_136 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_lookupLocal_360 v0 v1
  = coe
      d_lookupLocal'45'go_272 (coe d_size_150 (coe v0)) (coe v1)
      (coe d_named_152 (coe v0)) (coe d_debruijn_154 (coe v0))
-- Once.TypeCheck.Classify.LookupLocalView
d_LookupLocalView_370 a0 a1 = ()
data T_LookupLocalView_370
  = C_llv'45'found_382 MAlonzo.Code.Once.Type.T_Type_108
                       MAlonzo.Code.Once.Surface.Syntax.T_Usage_50
                       MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 |
    C_llv'45'not'45'found_384
-- Once.TypeCheck.Classify.inspectLookupLocal
d_inspectLookupLocal_390 ::
  T_NamedCtx_136 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupLocalView_370
d_inspectLookupLocal_390 v0 v1
  = let v2
          = d_lookupLocal'45'go_272
              (coe d_size_150 (coe v0)) (coe v1) (coe d_named_152 (coe v0))
              (coe d_debruijn_154 (coe v0)) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> case coe v3 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
                  -> case coe v5 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v6 v7
                         -> coe C_llv'45'found_382 v4 v6 v7
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_llv'45'not'45'found_384
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.LookupImportView
d_LookupImportView_420 a0 a1 = ()
data T_LookupImportView_420
  = C_liv'45'found_428 MAlonzo.Code.Once.Type.T_Type_108 |
    C_liv'45'not'45'found_430
-- Once.TypeCheck.Classify.inspectLookupImport
d_inspectLookupImport_436 ::
  T_NamedCtx_136 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_LookupImportView_420
d_inspectLookupImport_436 v0 v1
  = let v2
          = d_lookupImport_230 (coe d_imports_158 (coe v0)) (coe v1) in
    coe
      (case coe v2 of
         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v3
           -> coe C_liv'45'found_428 v3
         MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
           -> coe C_liv'45'not'45'found_430
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.composeArgB
d_composeArgB_458 ::
  T_NamedCtx_136 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_108
d_composeArgB_458 v0 v1 v2
  = let v3 = coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 in
    coe
      (case coe v1 of
         MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v4
           -> let v5
                    = let v5 = d_lookupPoly_14 (coe d_polys_160 (coe v0)) (coe v4) in
                      coe
                        (case coe v5 of
                           MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v6
                             -> case coe v6 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
                                    -> coe
                                         MAlonzo.Code.Once.Type.d_schemaArrowCodomain_852 (coe v7)
                                         (coe v2)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v5
                           _ -> MAlonzo.RTE.mazUnreachableError) in
              coe
                (case coe v4 of
                   l | (==) l ("fst" :: Data.Text.Text) ->
                       case coe v2 of
                         MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v6)
                         _ -> coe v5
                   l | (==) l ("id" :: Data.Text.Text) ->
                       coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v2)
                   l | (==) l ("snd" :: Data.Text.Text) ->
                       case coe v2 of
                         MAlonzo.Code.Once.Type.C__'42'__122 v6 v7
                           -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe v7)
                         _ -> coe v5
                   l | (==) l ("terminal" :: Data.Text.Text) ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                         (coe MAlonzo.Code.Once.Type.C_Unit_118)
                   _ -> coe v5)
         MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v4 v5
           -> case coe v4 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v6 v7
                  -> case coe v6 of
                       MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v8
                         -> case coe v8 of
                              l | (==) l ("compose" :: Data.Text.Text) ->
                                  let v9 = d_composeArgB_458 (coe v0) (coe v5) (coe v2) in
                                  coe
                                    (case coe v9 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v10
                                         -> coe d_composeArgB_458 (coe v0) (coe v7) (coe v10)
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18 -> coe v9
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> coe v3
                       _ -> coe v3
                _ -> coe v3
         _ -> coe v3)
-- Once.TypeCheck.Classify.findLocalVarUsage
d_findLocalVarUsage_556 ::
  T_NamedCtx_136 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_findLocalVarUsage_556 v0 v1
  = case coe v0 of
      C_mkCtx_162 v2 v3 v4 v5 v6 v7
        -> coe du_go_572 (coe v1) (coe v3) (coe v4)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify._.go
d_go_572 ::
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Integer ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  Integer ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_go_572 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 ~v7 v8 v9 = du_go_572 v6 v8 v9
du_go_572 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  [MAlonzo.Code.Once.TypeCheck.Context.T_Binding_6] ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  Maybe MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_go_572 v0 v1 v2
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
                                     (let v12 = coe du_go_572 (coe v0) (coe v4) (coe v6) in
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
d_PolyBuiltinApp_636 = ()
data T_PolyBuiltinApp_636
  = C_pba'45'id_638 | C_pba'45'fst_640 | C_pba'45'snd_642 |
    C_pba'45'terminal_644 | C_pba'45'inl_646 | C_pba'45'inr_648 |
    C_pba'45'initial_650 | C_pba'45'arr_652 |
    C_pba'45'pair'45'applied_654 | C_pba'45'compose'45'applied_656 |
    C_pba'45'case'45'applied_658 | C_pba'45'curry_660 |
    C_pba'45'apply_662 | C_pba'45'In_664 | C_pba'45'cata_666
-- Once.TypeCheck.Classify.classifyAppHead
d_classifyAppHead_668 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  Maybe T_PolyBuiltinApp_636
d_classifyAppHead_668 v0
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
                       then coe
                              seq (coe v4)
                              (coe
                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 (coe C_pba'45'id_638))
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
                                           then coe
                                                  seq (coe v7)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                     (coe C_pba'45'fst_640))
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
                                                                      (coe
                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                         (coe C_pba'45'snd_642))
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
                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                             (coe
                                                                                                C_pba'45'terminal_644))
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
                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                 (coe
                                                                                                                    C_pba'45'inl_646))
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
                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                     (coe
                                                                                                                                        C_pba'45'inr_648))
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
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                         (coe
                                                                                                                                                            C_pba'45'initial_650))
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
                                                                                                                                                                       ("arr"
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
                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                             (coe
                                                                                                                                                                                C_pba'45'arr_652))
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
                                                                                                                                                                                           ("curry"
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
                                                                                                                                                                                                 MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                 (coe
                                                                                                                                                                                                    C_pba'45'curry_660))
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
                                                                                                                                                                                                               ("apply"
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
                                                                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                     (coe
                                                                                                                                                                                                                        C_pba'45'apply_662))
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
                                                                                                                                                                                                                                   ("In"
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
                                                                                                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                                         (coe
                                                                                                                                                                                                                                            C_pba'45'In_664))
                                                                                                                                                                                                                               else coe
                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v34)
                                                                                                                                                                                                                                      (let v35
                                                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                 erased
                                                                                                                                                                                                                                                 (\ v35 ->
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
                                                                                                                                                                                                                                                 v35 of
                                                                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v36 v37
                                                                                                                                                                                                                                              -> if coe
                                                                                                                                                                                                                                                      v36
                                                                                                                                                                                                                                                   then coe
                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             v37)
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                                                                                                                                                                                             (coe
                                                                                                                                                                                                                                                                C_pba'45'cata_666))
                                                                                                                                                                                                                                                   else coe
                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             v37)
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
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
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v1 v2
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
                              then coe
                                     seq (coe v6)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                        (coe C_pba'45'pair'45'applied_654))
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
                                                         (coe
                                                            MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                            (coe C_pba'45'compose'45'applied_656))
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
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_just_16
                                                                                (coe
                                                                                   C_pba'45'case'45'applied_658))
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18)
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v3 v4 v5 v6 v7
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v3
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v3 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v3 v4 v5
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v4
               -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v1 v2 v3 v4 v5
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v1
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v1 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v1 v2 v3
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v2
        -> coe MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.AppHeadView
d_AppHeadView_794 a0 = ()
data T_AppHeadView_794
  = C_ahv'45'id_796 | C_ahv'45'fst_798 | C_ahv'45'snd_800 |
    C_ahv'45'terminal_802 | C_ahv'45'inl_804 | C_ahv'45'inr_806 |
    C_ahv'45'initial_808 | C_ahv'45'arr_810 | C_ahv'45'curry_812 |
    C_ahv'45'apply_814 | C_ahv'45'In_816 | C_ahv'45'cata_818 |
    C_ahv'45'pair'45'applied_822 | C_ahv'45'compose'45'applied_826 |
    C_ahv'45'case'45'applied_830 | C_ahv'45'other_834
-- Once.TypeCheck.Classify.classifyAppHeadView
d_classifyAppHeadView_838 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> T_AppHeadView_794
d_classifyAppHeadView_838 v0
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
                       then coe seq (coe v4) (coe C_ahv'45'id_796)
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
                                           then coe seq (coe v7) (coe C_ahv'45'fst_798)
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
                                                                      (coe C_ahv'45'snd_800)
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
                                                                                             C_ahv'45'terminal_802)
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
                                                                                                                 C_ahv'45'inl_804)
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
                                                                                                                                     C_ahv'45'inr_806)
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
                                                                                                                                                         C_ahv'45'initial_808)
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
                                                                                                                                                                       ("arr"
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
                                                                                                                                                                             C_ahv'45'arr_810)
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
                                                                                                                                                                                           ("curry"
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
                                                                                                                                                                                                 C_ahv'45'curry_812)
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
                                                                                                                                                                                                               ("apply"
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
                                                                                                                                                                                                                     C_ahv'45'apply_814)
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
                                                                                                                                                                                                                                   ("In"
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
                                                                                                                                                                                                                                         C_ahv'45'In_816)
                                                                                                                                                                                                                               else coe
                                                                                                                                                                                                                                      seq
                                                                                                                                                                                                                                      (coe
                                                                                                                                                                                                                                         v34)
                                                                                                                                                                                                                                      (let v35
                                                                                                                                                                                                                                             = coe
                                                                                                                                                                                                                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.du_map'8242'_178
                                                                                                                                                                                                                                                 erased
                                                                                                                                                                                                                                                 (\ v35 ->
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
                                                                                                                                                                                                                                                 v35 of
                                                                                                                                                                                                                                            MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v36 v37
                                                                                                                                                                                                                                              -> if coe
                                                                                                                                                                                                                                                      v36
                                                                                                                                                                                                                                                   then coe
                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             v37)
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             C_ahv'45'cata_818)
                                                                                                                                                                                                                                                   else coe
                                                                                                                                                                                                                                                          seq
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             v37)
                                                                                                                                                                                                                                                          (coe
                                                                                                                                                                                                                                                             C_ahv'45'other_834)
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
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v1 v2
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v1 v2
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
                              then coe seq (coe v6) (coe C_ahv'45'pair'45'applied_822)
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
                                                         (coe C_ahv'45'compose'45'applied_826)
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
                                                                                C_ahv'45'case'45'applied_830)
                                                                      else coe
                                                                             seq (coe v12)
                                                                             (coe
                                                                                C_ahv'45'other_834)
                                                               _ -> MAlonzo.RTE.mazUnreachableError))
                                           _ -> MAlonzo.RTE.mazUnreachableError))
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v3 v4
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_40 v3 v4
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v3 v4
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v3 v4 v5
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v3 v4
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v3 v4 v5 v6 v7
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v3
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v3
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v3 v4
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v3 v4 v5
               -> coe C_ahv'45'other_834
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v4
               -> coe C_ahv'45'other_834
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_42 v1 v2
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_44 v1 v2 v3
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_46 v1 v2
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_48 v1 v2 v3 v4 v5
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnit_50
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_52 v1
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_54 v1
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_56 v1 v2
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_58 v1 v2 v3
        -> coe C_ahv'45'other_834
      MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_60 v2
        -> coe C_ahv'45'other_834
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.Classify.classifyAppHead-nothing⇒view-other
d_classifyAppHead'45'nothing'8658'view'45'other_966 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_classifyAppHead'45'nothing'8658'view'45'other_966 = erased
-- Once.TypeCheck.Classify.view-other⇒classifyAppHead-nothing
d_view'45'other'8658'classifyAppHead'45'nothing_1274 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_view'45'other'8658'classifyAppHead'45'nothing_1274 = erased
-- Once.TypeCheck.Classify.BareBuiltinClass
d_BareBuiltinClass_1580 a0 = ()
data T_BareBuiltinClass_1580
  = C_bbc'45'id_1582 | C_bbc'45'fst_1584 | C_bbc'45'snd_1586 |
    C_bbc'45'terminal_1588 | C_bbc'45'initial_1590 |
    C_bbc'45'inl_1592 | C_bbc'45'inr_1594 | C_bbc'45'arr_1596 |
    C_bbc'45'other_1600
-- Once.TypeCheck.Classify.classifyBareBuiltin
d_classifyBareBuiltin_1604 ::
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  T_BareBuiltinClass_1580
d_classifyBareBuiltin_1604 v0
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
                then coe seq (coe v3) (coe C_bbc'45'id_1582)
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
                                    then coe seq (coe v6) (coe C_bbc'45'fst_1584)
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
                                                               seq (coe v9) (coe C_bbc'45'snd_1586)
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
                                                                                      C_bbc'45'terminal_1588)
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
                                                                                                          C_bbc'45'initial_1590)
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
                                                                                                                              C_bbc'45'inl_1592)
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
                                                                                                                                                  C_bbc'45'inr_1594)
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
                                                                                                                                                                  v0))
                                                                                                                                                          (coe
                                                                                                                                                             MAlonzo.Code.Data.String.Properties.d__'8776''63'__28
                                                                                                                                                             (coe
                                                                                                                                                                v0)
                                                                                                                                                             (coe
                                                                                                                                                                ("arr"
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
                                                                                                                                                                      C_bbc'45'arr_1596)
                                                                                                                                                            else coe
                                                                                                                                                                   seq
                                                                                                                                                                   (coe
                                                                                                                                                                      v24)
                                                                                                                                                                   (coe
                                                                                                                                                                      C_bbc'45'other_1600)
                                                                                                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                                             _ -> MAlonzo.RTE.mazUnreachableError))
                                                                                         _ -> MAlonzo.RTE.mazUnreachableError))
                                                                     _ -> MAlonzo.RTE.mazUnreachableError))
                                                 _ -> MAlonzo.RTE.mazUnreachableError))
                             _ -> MAlonzo.RTE.mazUnreachableError))
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.TypeCheck.Classify.ViewBundle
d_ViewBundle_1672 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 -> ()
d_ViewBundle_1672 = erased
-- Once.TypeCheck.Classify.viewBundle
d_viewBundle_1680 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_viewBundle_1680 v0
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe d_classifyAppHeadView_838 (coe v0)) erased
