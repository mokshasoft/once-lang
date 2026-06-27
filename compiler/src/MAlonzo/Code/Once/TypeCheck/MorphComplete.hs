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

module MAlonzo.Code.Once.TypeCheck.MorphComplete where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Maybe
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Elaborate
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Relation.Nullary.Decidable.Core

-- Once.TypeCheck.MorphComplete.just≢nothing
d_just'8802'nothing_10 ::
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_10 = erased
-- Once.TypeCheck.MorphComplete.StrongElab
d_StrongElab_22 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 -> ()
d_StrongElab_22 = erased
-- Once.TypeCheck.MorphComplete.go-canonical
d_go'45'canonical_62 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  Maybe MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_go'45'canonical_62 = erased
-- Once.TypeCheck.MorphComplete.composeGo-success
d_composeGo'45'success_110 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  Integer ->
  Integer ->
  Integer ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_composeGo'45'success_110 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7 v8 ~v9
                           ~v10 ~v11 ~v12 ~v13 ~v14 v15 v16 v17 ~v18 ~v19 ~v20 ~v21 ~v22 ~v23
                           ~v24 ~v25
  = du_composeGo'45'success_110 v6 v7 v8 v15 v16 v17
du_composeGo'45'success_110 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_composeGo'45'success_110 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe MAlonzo.Code.Once.IR.C__'8728'__30 v0 v1 v2)
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
         (coe
            addInt (coe (1 :: Integer))
            (coe MAlonzo.Code.Data.Nat.Base.d__'8852'__208 (coe v3) (coe v5)))
         (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) erased))
-- Once.TypeCheck.MorphComplete.const-morph-strong
d_const'45'morph'45'strong_158
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.MorphComplete.const-morph-strong"
-- Once.TypeCheck.MorphComplete.cata-morph-strong
d_cata'45'morph'45'strong_172
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.MorphComplete.cata-morph-strong"
-- Once.TypeCheck.MorphComplete.named-morph-strong
d_named'45'morph'45'strong_184
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.MorphComplete.named-morph-strong"
-- Once.TypeCheck.MorphComplete.named-morph-strong-resolved
d_named'45'morph'45'strong'45'resolved_196
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.TypeCheck.MorphComplete.named-morph-strong-resolved"
-- Once.TypeCheck.MorphComplete.morph-elab
d_morph'45'elab_208 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_morph'45'elab_208 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_356
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                     (coe v0) (coe ("id" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("id" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("id" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("id" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v14 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                               -> case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v15
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("id" :: Data.Text.Text)) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v16
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
                                                      (coe v2) (coe v2) in
                                            coe
                                              (case coe v16 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v17 v18
                                                   -> if coe v17
                                                        then coe
                                                               seq (coe v18)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe MAlonzo.Code.Once.IR.C_id_22)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_356)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_id_22))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_356))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       erased))))))))
                                                        else coe
                                                               seq (coe v18)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_366
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                     (coe v0) (coe ("fst" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("fst" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("fst" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("fst" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("fst" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
                                                      (coe v3) (coe v3) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_fst_44)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_366)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_fst_44))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_366))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       erased))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_376
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                     (coe v0) (coe ("snd" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("snd" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("snd" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("snd" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("snd" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
                                                      (coe v3) (coe v3) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_snd_50)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_376)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_snd_50))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_376))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       erased))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_384
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                     (coe v0) (coe ("terminal" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("terminal" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("terminal" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v14 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                               -> case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v15
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("terminal" :: Data.Text.Text)) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.IR.C_terminal_74)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_384)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                       (coe MAlonzo.Code.Once.IR.C_terminal_74))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_384))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased erased)))))))
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_392
        -> let v11
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                     (coe v0) (coe ("initial" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("initial" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("initial" :: Data.Text.Text))) in
           coe
             (case coe v11 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v12 v13
                  -> coe
                       seq (coe v12)
                       (let v14
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("initial" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v14 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v15
                               -> case coe v15 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                      -> coe
                                           seq (coe v17)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v15
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("initial" :: Data.Text.Text)) in
                                  coe
                                    (case coe v15 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                              (coe MAlonzo.Code.Once.IR.C_initial_78)
                                              (coe
                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                 (coe
                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_392)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    (coe
                                                       MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                       (coe MAlonzo.Code.Once.IR.C_initial_78))
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe (0 :: Integer))
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                             (coe v0))
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe
                                                                MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                (coe
                                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_392))
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased erased)))))))
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_402
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                     (coe v0) (coe ("inl" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("inl" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("inl" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("inl" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("inl" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
                                                      (coe v2) (coe v2) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_inl_56
                                                                     (coe
                                                                        MAlonzo.Code.Once.IR.C_Heap_8))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_402)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inl_56
                                                                              (coe
                                                                                 MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_402))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       erased))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_412
        -> let v12
                 = coe
                     MAlonzo.Code.Once.TypeCheck.Elaborate.du_inferElabV'45'RVar'45'lookup'45'aux_1546
                     (coe v0) (coe ("inr" :: Data.Text.Text))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                        (coe ("inr" :: Data.Text.Text))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190 (coe v0)))
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                        (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194 (coe v0))
                        (coe ("inr" :: Data.Text.Text))) in
           coe
             (case coe v12 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                  -> coe
                       seq (coe v13)
                       (let v15
                              = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupLocal'45'go_316
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_size_186 (coe v0))
                                  (coe ("inr" :: Data.Text.Text))
                                  (coe MAlonzo.Code.Once.TypeCheck.Classify.d_named_188 (coe v0))
                                  (coe
                                     MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_190
                                     (coe v0)) in
                        coe
                          (case coe v15 of
                             MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v16
                               -> case coe v16 of
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                      -> coe
                                           seq (coe v18)
                                           (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                    _ -> MAlonzo.RTE.mazUnreachableError
                             MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                               -> let v16
                                        = MAlonzo.Code.Once.TypeCheck.Classify.d_lookupImport_274
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_194
                                               (coe v0))
                                            (coe ("inr" :: Data.Text.Text)) in
                                  coe
                                    (case coe v16 of
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_just_16 v17
                                         -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                       MAlonzo.Code.Agda.Builtin.Maybe.C_nothing_18
                                         -> let v17
                                                  = MAlonzo.Code.Once.TypeCheck.Elaborate.d__'8799'T__220
                                                      (coe v2) (coe v2) in
                                            coe
                                              (case coe v17 of
                                                 MAlonzo.Code.Relation.Nullary.Decidable.Core.C__because__32 v18 v19
                                                   -> if coe v18
                                                        then coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                  (coe
                                                                     MAlonzo.Code.Once.IR.C_inr_62
                                                                     (coe
                                                                        MAlonzo.Code.Once.IR.C_Heap_8))
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     (coe
                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_412)
                                                                     (coe
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                        (coe
                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                           (coe
                                                                              MAlonzo.Code.Once.IR.C_inr_62
                                                                              (coe
                                                                                 MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           (coe (0 :: Integer))
                                                                           (coe
                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                              (coe
                                                                                 MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_192
                                                                                 (coe v0))
                                                                              (coe
                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                 (coe
                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                    (coe
                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_412))
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    (coe
                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                       erased
                                                                                       erased))))))))
                                                        else coe
                                                               seq (coe v19)
                                                               (coe
                                                                  MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                 _ -> MAlonzo.RTE.mazUnreachableError)
                                       _ -> MAlonzo.RTE.mazUnreachableError)
                             _ -> MAlonzo.RTE.mazUnreachableError))
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_428 v10 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v18 v19
                      -> let v20
                               = d_morph'45'elab_208
                                   (coe v0) (coe v19) (coe v10) (coe v3) (coe v4) (coe v14) in
                         coe
                           (let v21
                                  = d_morph'45'elab_208
                                      (coe v0) (coe v17) (coe v2) (coe v10) (coe v4) (coe v15) in
                            coe
                              (case coe v20 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                   -> case coe v23 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                          -> case coe v25 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                 -> case coe v27 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                        -> case coe v29 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                               -> case coe v31 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                      -> case coe v33 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                             -> coe
                                                                                  seq (coe v35)
                                                                                  (case coe v21 of
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                       -> case coe
                                                                                                 v37 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                              -> case coe
                                                                                                        v39 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                     -> case coe
                                                                                                               v41 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                            -> case coe
                                                                                                                      v43 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                                                                                                   -> case coe
                                                                                                                             v45 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                                                                                          -> case coe
                                                                                                                                    v47 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v48 v49
                                                                                                                                 -> coe
                                                                                                                                      seq
                                                                                                                                      (coe
                                                                                                                                         v49)
                                                                                                                                      (coe
                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                            v10
                                                                                                                                            v22
                                                                                                                                            v36)
                                                                                                                                         (coe
                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_428
                                                                                                                                               v10
                                                                                                                                               v24
                                                                                                                                               v38)
                                                                                                                                            (coe
                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Once.IR.C__'8728'__30
                                                                                                                                                     v10
                                                                                                                                                     v22
                                                                                                                                                     v36))
                                                                                                                                               (coe
                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                  (coe
                                                                                                                                                     addInt
                                                                                                                                                     (coe
                                                                                                                                                        (1 ::
                                                                                                                                                           Integer))
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                        (coe
                                                                                                                                                           v28)
                                                                                                                                                        (coe
                                                                                                                                                           v42)))
                                                                                                                                                  (coe
                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                     (coe
                                                                                                                                                        v30)
                                                                                                                                                     (coe
                                                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_428
                                                                                                                                                              v10
                                                                                                                                                              v24
                                                                                                                                                              v38))
                                                                                                                                                        (coe
                                                                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                           erased
                                                                                                                                                           (coe
                                                                                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                              erased
                                                                                                                                                              erased))))))))
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_444 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v19 v20
                             -> let v21
                                      = d_morph'45'elab_208
                                          (coe v0) (coe v18) (coe v19) (coe v3) (coe v4)
                                          (coe v13) in
                                coe
                                  (let v22
                                         = d_morph'45'elab_208
                                             (coe v0) (coe v16) (coe v20) (coe v3) (coe v4)
                                             (coe v14) in
                                   coe
                                     (case coe v21 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                                          -> case coe v24 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                                 -> case coe v26 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                                        -> case coe v28 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                                               -> case coe v30 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                                                      -> case coe v32 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                                             -> case coe v34 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v36)
                                                                                         (case coe
                                                                                                 v22 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                                                              -> case coe
                                                                                                        v38 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                                                                     -> case coe
                                                                                                               v40 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                                                                            -> case coe
                                                                                                                      v42 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                                                                                                   -> case coe
                                                                                                                             v44 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v45 v46
                                                                                                                          -> case coe
                                                                                                                                    v46 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v47 v48
                                                                                                                                 -> case coe
                                                                                                                                           v48 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v49 v50
                                                                                                                                        -> coe
                                                                                                                                             seq
                                                                                                                                             (coe
                                                                                                                                                v50)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                   v23
                                                                                                                                                   v37)
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_444
                                                                                                                                                      v25
                                                                                                                                                      v39)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Once.IR.C_case_70
                                                                                                                                                            v23
                                                                                                                                                            v37))
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                         (coe
                                                                                                                                                            addInt
                                                                                                                                                            (coe
                                                                                                                                                               (1 ::
                                                                                                                                                                  Integer))
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                               (coe
                                                                                                                                                                  v29)
                                                                                                                                                               (coe
                                                                                                                                                                  v43)))
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                            (coe
                                                                                                                                                               v31)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_444
                                                                                                                                                                     v25
                                                                                                                                                                     v39))
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                  erased
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                     erased
                                                                                                                                                                     erased))))))))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_458 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                             -> let v20
                                      = d_morph'45'elab_208
                                          (coe v0) (coe v17) (coe v2) (coe v18)
                                          (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v12) in
                                coe
                                  (let v21
                                         = d_morph'45'elab_208
                                             (coe v0) (coe v15) (coe v2) (coe v19)
                                             (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v13) in
                                   coe
                                     (case coe v20 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                          -> case coe v23 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                 -> case coe v25 of
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                        -> case coe v27 of
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                               -> case coe v29 of
                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                      -> case coe v31 of
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                                             -> case coe v33 of
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                                                                    -> coe
                                                                                         seq
                                                                                         (coe v35)
                                                                                         (case coe
                                                                                                 v21 of
                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                                                              -> case coe
                                                                                                        v37 of
                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                                                                     -> case coe
                                                                                                               v39 of
                                                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                                                                            -> case coe
                                                                                                                      v41 of
                                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                                                                   -> case coe
                                                                                                                             v43 of
                                                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                                                                                                          -> case coe
                                                                                                                                    v45 of
                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                                                                                                 -> case coe
                                                                                                                                           v47 of
                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v48 v49
                                                                                                                                        -> coe
                                                                                                                                             seq
                                                                                                                                             (coe
                                                                                                                                                v49)
                                                                                                                                             (coe
                                                                                                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                                                                                                   v22
                                                                                                                                                   v36
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Once.IR.C_Heap_8))
                                                                                                                                                (coe
                                                                                                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_458
                                                                                                                                                      v24
                                                                                                                                                      v38)
                                                                                                                                                   (coe
                                                                                                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38
                                                                                                                                                            v22
                                                                                                                                                            v36
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                                                                                                      (coe
                                                                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                         (coe
                                                                                                                                                            addInt
                                                                                                                                                            (coe
                                                                                                                                                               (1 ::
                                                                                                                                                                  Integer))
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Data.Nat.Base.d__'8852'__208
                                                                                                                                                               (coe
                                                                                                                                                                  v28)
                                                                                                                                                               (coe
                                                                                                                                                                  v42)))
                                                                                                                                                         (coe
                                                                                                                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                            (coe
                                                                                                                                                               v44)
                                                                                                                                                            (coe
                                                                                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_458
                                                                                                                                                                     v24
                                                                                                                                                                     v38))
                                                                                                                                                               (coe
                                                                                                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                  erased
                                                                                                                                                                  (coe
                                                                                                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                                                                                     erased
                                                                                                                                                                     erased))))))))
                                                                                                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                                                            _ -> MAlonzo.RTE.mazUnreachableError)
                                                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                      _ -> MAlonzo.RTE.mazUnreachableError
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_470 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
                      -> let v17
                               = d_morph'45'elab_208
                                   (coe v0) (coe v13)
                                   (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v14))
                                   (coe v16) (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v11) in
                         coe
                           (case coe v17 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                -> case coe v19 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                       -> case coe v21 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                              -> case coe v23 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                     -> case coe v25 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                            -> case coe v27 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                   -> case coe v29 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                                                          -> coe
                                                                               seq (coe v31)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.IR.C_curry_88
                                                                                     v18
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.IR.C_Heap_8))
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_470
                                                                                        v20)
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534
                                                                                           (coe
                                                                                              MAlonzo.Code.Once.IR.C_curry_88
                                                                                              v18
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.IR.C_Heap_8)))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe
                                                                                              addInt
                                                                                              (coe
                                                                                                 (1 ::
                                                                                                    Integer))
                                                                                              (coe
                                                                                                 v24))
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 v26)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_540
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_470
                                                                                                       v20))
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    erased
                                                                                                    (coe
                                                                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                       erased
                                                                                                       erased))))))))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_484 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v16
                      -> coe
                           d_cata'45'morph'45'strong_172 v0 v15 v16 v3 v4 v11 erased v13
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'arr_494 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> let v13
                        = d_morph'45'elab_208
                            (coe v0) (coe v12) (coe v2) (coe v3)
                            (coe MAlonzo.Code.Once.Type.C_pure_34) (coe v10) in
                  coe
                    (case coe v13 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v14 v15
                         -> case coe v15 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v16 v17
                                -> case coe v17 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v18 v19
                                       -> case coe v19 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v20 v21
                                              -> case coe v21 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v22 v23
                                                     -> case coe v23 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                                                            -> case coe v25 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                                                   -> case coe v27 of
                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                                                          -> coe
                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                               (coe v14)
                                                                               (coe
                                                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                  (coe
                                                                                     MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'arr_494
                                                                                     v16)
                                                                                  (coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     (coe
                                                                                        MAlonzo.Code.Once.Surface.Syntax.C_arr''_496
                                                                                        v18)
                                                                                     (coe
                                                                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                        (coe
                                                                                           addInt
                                                                                           (coe
                                                                                              (1 ::
                                                                                                 Integer))
                                                                                           (coe
                                                                                              v20))
                                                                                        (coe
                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                           (coe v22)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              (coe
                                                                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arr'45'app'45'check_664
                                                                                                 v24)
                                                                                              (coe
                                                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                 erased
                                                                                                 (coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    (coe
                                                                                                       v28)
                                                                                                    erased)))))))
                                                                        _ -> MAlonzo.RTE.mazUnreachableError
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_504 v10
        -> coe d_const'45'morph'45'strong_158 v0 v1 v2 v3 v10
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_516
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v14
               -> coe
                    d_named'45'morph'45'strong_184 v0 v14 v2 v3 v4 erased erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_528
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v12
               -> coe
                    d_named'45'morph'45'strong'45'resolved_196 v0 v12 v2 v3 v4 erased
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.MorphComplete.morph-complete
d_morph'45'complete_1038 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_170 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_morph'45'complete_1038 v0 v1 v2 v3 v4 v5
  = let v6
          = d_morph'45'elab_208
              (coe v0) (coe v1) (coe v2) (coe v3) (coe v4) (coe v5) in
    coe
      (case coe v6 of
         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v7 v8
           -> case coe v8 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                  -> case coe v10 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                         -> case coe v12 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                                -> case coe v14 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                       -> case coe v16 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v17 v18
                                              -> case coe v18 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v19 v20
                                                     -> coe
                                                          seq (coe v20)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             (coe v11)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                (coe v13)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   (coe v15) erased)))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError
         _ -> MAlonzo.RTE.mazUnreachableError)
