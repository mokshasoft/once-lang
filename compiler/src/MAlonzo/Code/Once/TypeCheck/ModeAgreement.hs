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

module MAlonzo.Code.Once.TypeCheck.ModeAgreement where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Context
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.ModeAgreement.just≢nothing
d_just'8802'nothing_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_12 = erased
-- Once.TypeCheck.ModeAgreement.cod-≡
d_cod'45''8801'_26 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cod'45''8801'_26 = erased
-- Once.TypeCheck.ModeAgreement.arith-not-cmp
d_arith'45'not'45'cmp_30 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_arith'45'not'45'cmp_30 = erased
-- Once.TypeCheck.ModeAgreement.extractGroundF-irr
d_extractGroundF'45'irr_38 ::
  MAlonzo.Code.Once.Type.T_PolyFunctor_244 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractGroundF'45'irr_38 = erased
-- Once.TypeCheck.ModeAgreement.extractGround-irr
d_extractGround'45'irr_46 ::
  MAlonzo.Code.Once.Type.T_PolyType_246 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractGround'45'irr_46 = erased
-- Once.TypeCheck.ModeAgreement.noinf-id
d_noinf'45'id_158 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'id_158 = erased
-- Once.TypeCheck.ModeAgreement.noinf-fst
d_noinf'45'fst_168 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'fst_168 = erased
-- Once.TypeCheck.ModeAgreement.noinf-snd
d_noinf'45'snd_178 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'snd_178 = erased
-- Once.TypeCheck.ModeAgreement.noinf-terminal
d_noinf'45'terminal_188 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'terminal_188 = erased
-- Once.TypeCheck.ModeAgreement.noinf-initial
d_noinf'45'initial_198 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'initial_198 = erased
-- Once.TypeCheck.ModeAgreement.noinf-inl
d_noinf'45'inl_208 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inl_208 = erased
-- Once.TypeCheck.ModeAgreement.noinf-inr
d_noinf'45'inr_218 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inr_218 = erased
-- Once.TypeCheck.ModeAgreement.noinf-curry-app
d_noinf'45'curry'45'app_230 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'curry'45'app_230 = erased
-- Once.TypeCheck.ModeAgreement.noinf-cata-app
d_noinf'45'cata'45'app_240 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'cata'45'app_240 = erased
-- Once.TypeCheck.ModeAgreement.noinf-ana-app
d_noinf'45'ana'45'app_250 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'ana'45'app_250 = erased
-- Once.TypeCheck.ModeAgreement.noinf-In-app
d_noinf'45'In'45'app_260 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'In'45'app_260 = erased
-- Once.TypeCheck.ModeAgreement.noinf-inl-app
d_noinf'45'inl'45'app_270 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inl'45'app_270 = erased
-- Once.TypeCheck.ModeAgreement.noinf-inr-app
d_noinf'45'inr'45'app_280 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inr'45'app_280 = erased
-- Once.TypeCheck.ModeAgreement.noinf-initial-app
d_noinf'45'initial'45'app_290 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'initial'45'app_290 = erased
-- Once.TypeCheck.ModeAgreement.noinf-compose
d_noinf'45'compose_302 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'compose_302 = erased
-- Once.TypeCheck.ModeAgreement.noinf-case
d_noinf'45'case_314 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'case_314 = erased
-- Once.TypeCheck.ModeAgreement.noinf-pair
d_noinf'45'pair_326 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'pair_326 = erased
-- Once.TypeCheck.ModeAgreement.agree-ii
d_agree'45'ii_340 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree'45'ii_340 v0 v1 v2 v3 ~v4 ~v5 v6 v7
  = du_agree'45'ii_340 v0 v1 v2 v3 v6 v7
du_agree'45'ii_340 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree'45'ii_340 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v10 v12 v13
               -> case coe v10 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v16 v17
                      -> case coe v17 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v20 v21
                             -> case coe v21 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v24 v25
                                    -> case coe v25 of
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v28 v29
                                           -> case coe v29 of
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v32 v33
                                                  -> case coe v33 of
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v36 v37
                                                         -> case coe v37 of
                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v40 v41
                                                                -> coe
                                                                     seq (coe v41)
                                                                     (coe
                                                                        MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
                                                              _ -> MAlonzo.RTE.mazUnreachableError
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v10
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v16
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v18 v19
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v15 v16 v17 v18 v22 v24
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v11 v12
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v9 v11 v12
        -> let v13
                 = seq
                     (coe v5)
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased) in
           coe
             (case coe v9 of
                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v16 v17
                  -> let v18
                           = seq
                               (coe v5)
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased) in
                     coe
                       (case coe v17 of
                          MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v21 v22
                            -> let v23
                                     = seq
                                         (coe v5)
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                            erased) in
                               coe
                                 (case coe v22 of
                                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v26 v27
                                      -> let v28
                                               = seq
                                                   (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      erased erased) in
                                         coe
                                           (case coe v27 of
                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v31 v32
                                                -> let v33
                                                         = seq
                                                             (coe v5)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased erased) in
                                                   coe
                                                     (case coe v32 of
                                                        MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v36 v37
                                                          -> let v38
                                                                   = seq
                                                                       (coe v5)
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          erased erased) in
                                                             coe
                                                               (case coe v37 of
                                                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v41 v42
                                                                    -> let v43
                                                                             = seq
                                                                                 (coe v5)
                                                                                 (coe
                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                    erased
                                                                                    erased) in
                                                                       coe
                                                                         (case coe v42 of
                                                                            MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v46 v47
                                                                              -> let v48
                                                                                       = seq
                                                                                           (coe v5)
                                                                                           (coe
                                                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                              erased
                                                                                              erased) in
                                                                                 coe
                                                                                   (case coe v47 of
                                                                                      MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v51 v52
                                                                                        -> case coe
                                                                                                  v5 of
                                                                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v56 v58 v59
                                                                                               -> coe
                                                                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                    erased
                                                                                                    erased
                                                                                             _ -> MAlonzo.RTE.mazUnreachableError
                                                                                      _ -> coe v48)
                                                                            _ -> coe v43)
                                                                  _ -> coe v38)
                                                        _ -> coe v33)
                                              _ -> coe v28)
                                    _ -> coe v23)
                          _ -> coe v18)
                _ -> coe v13)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v12 v13
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v20 v21
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v17 v18 v19 v20 v24 v26
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v9 v10 v11 v12 v16 v18
        -> case coe v5 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v23
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v25 v26
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v22 v23 v24 v25 v29 v31
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v10
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v17 v18
                      -> case coe v5 of
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v24 v25 v26 v27
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Type.C__'42'__122 v28 v29
                                    -> let v30
                                             = coe
                                                 du_agree'45'ii_340 (coe v0) (coe v15) (coe v17)
                                                 (coe v28) (coe v13) (coe v26) in
                                       coe
                                         (let v31
                                                = coe
                                                    du_agree'45'ii_340 (coe v0) (coe v16) (coe v18)
                                                    (coe v29) (coe v14) (coe v27) in
                                          coe
                                            (coe
                                               seq (coe v30)
                                               (coe
                                                  seq (coe v31)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                     erased erased))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 du_agree'45'ii_340 (coe v0) (coe v11)
                                 (coe MAlonzo.Code.Once.Type.C_Int_132)
                                 (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9) (coe v15)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'float_156
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v10 v12 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v17 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_176 v24 v26 v27 v28 v29 v30
                      -> let v31
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v18) (coe v10) (coe v24)
                                   (coe v15) (coe v29) in
                         coe
                           (coe
                              seq (coe v31)
                              (let v32
                                     = coe
                                         du_agree'45'ii_340
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                            (coe
                                               addInt (coe (1 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                                                  (coe v17) (coe v10)
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_named_320
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                               (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322
                                                  (coe v0))
                                               v10 (coe MAlonzo.Code.Once.Type.C_Many_10))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328
                                               (coe v0)))
                                         (coe v19) (coe v2) (coe v3) (coe v16) (coe v30) in
                               coe
                                 (coe
                                    seq (coe v32)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v12 v13 v15 v16 v17 v18 v19 v20 v21 v22
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v23 v24 v25 v26 v27
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_206 v34 v35 v37 v38 v39 v40 v41 v42 v43 v44
                      -> let v45
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v23)
                                   (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v12) (coe v13))
                                   (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v34) (coe v35))
                                   (coe v20) (coe v42) in
                         coe
                           (coe
                              seq (coe v45)
                              (let v46
                                     = coe
                                         du_agree'45'ii_340
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                            (coe
                                               addInt (coe (1 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                                                  (coe v24) (coe v12)
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_named_320
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                               (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322
                                                  (coe v0))
                                               v12 (coe MAlonzo.Code.Once.Type.C_Many_10))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328
                                               (coe v0)))
                                         (coe v25) (coe v2) (coe v3) (coe v21) (coe v43) in
                               coe
                                 (let v47
                                        = coe
                                            du_agree'45'ii_340
                                            (coe
                                               MAlonzo.Code.Once.TypeCheck.Classify.C_mkCtx_330
                                               (coe
                                                  addInt (coe (1 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_size_318
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Context.C_mkBinding_20
                                                     (coe v26) (coe v13)
                                                     (coe MAlonzo.Code.Once.Type.C_Many_10))
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.Classify.d_named_320
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12
                                                  (MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_322
                                                     (coe v0))
                                                  v13 (coe MAlonzo.Code.Once.Type.C_Many_10))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_freshCounter_324
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_imports_326
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.TypeCheck.Classify.d_polys_328
                                                  (coe v0)))
                                            (coe v27) (coe v2) (coe v3) (coe v22) (coe v44) in
                                  coe
                                    (coe
                                       seq (coe v46)
                                       (coe
                                          seq (coe v47)
                                          (coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                             erased))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Type.C_Int_132)
                                   (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_340 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Type.C_Int_132)
                                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v14) (coe v26) in
                            coe
                              (coe
                                 seq (coe v27)
                                 (coe
                                    seq (coe v28)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v22 v23 v25 v26
                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float_234 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Type.C_Float_134)
                                   (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_340 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Type.C_Float_134)
                                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v14)
                                      (coe v26) in
                            coe
                              (coe
                                 seq (coe v27)
                                 (coe
                                    seq (coe v28)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'il_248 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Type.C_Int_132)
                                   (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_340 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Type.C_Float_134)
                                      (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v14)
                                      (coe v26) in
                            coe
                              (coe
                                 seq (coe v27)
                                 (coe
                                    seq (coe v28)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith'45'float'45'ir_262 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Type.C_Float_134)
                                   (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_340 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Type.C_Int_132)
                                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v14) (coe v26) in
                            coe
                              (coe
                                 seq (coe v27)
                                 (coe
                                    seq (coe v28)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_220 v22 v23 v25 v26
                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_276 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Type.C_Int_132)
                                   (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_340 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Type.C_Int_132)
                                      (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v14) (coe v26) in
                            coe
                              (coe
                                 seq (coe v27)
                                 (coe
                                    seq (coe v28)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_286 v16 v17
                      -> let v18
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v12) (coe v2) (coe v3) (coe v10)
                                   (coe v17) in
                         coe
                           (coe
                              seq (coe v18)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_298 v17 v18 v19
                      -> let v20
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v13)
                                   (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v9))
                                   (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v3) (coe v17))
                                   (coe v11) (coe v19) in
                         coe
                           (coe
                              seq (coe v20)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_310 v16 v18 v19
                      -> let v20
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v13)
                                   (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v8) (coe v2))
                                   (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v16) (coe v3))
                                   (coe v11) (coe v19) in
                         coe
                           (coe
                              seq (coe v20)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_320 v15 v16 v17
                      -> let v18
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v12) (coe v8) (coe v15)
                                   (coe v10) (coe v17) in
                         coe
                           (coe
                              seq (coe v18)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_332 v16 v18 v19
                      -> let v20
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'42'__122
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                            (coe MAlonzo.Code.Once.Type.C_pure_34))
                                         (coe v2))
                                      (coe v8))
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'42'__122
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v16)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                            (coe MAlonzo.Code.Once.Type.C_pure_34))
                                         (coe v3))
                                      (coe v16))
                                   (coe v11) (coe v19) in
                         coe
                           (coe
                              seq (coe v20)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_344 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
                      -> case coe v5 of
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_344 v19 v21 v22
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v23 v24 v25
                                    -> let v26
                                             = coe
                                                 du_agree'45'ii_340 (coe v0) (coe v13)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'42'__122
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v8)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                       (coe v16))
                                                    (coe v8))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'42'__122
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                       (coe v19)
                                                       (coe
                                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                       (coe v25))
                                                    (coe v19))
                                                 (coe v11) (coe v22) in
                                       coe
                                         (coe
                                            seq (coe v26)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_356 v8 v10 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'infer_356 v18 v20 v21 v23
                      -> let v24
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v15)
                                   (coe
                                      MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v8)
                                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                                   (coe
                                      MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v18)
                                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                                   (coe v13) (coe v23) in
                         coe
                           (coe
                              seq (coe v24)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_368 v18 v20 v21 v23
                      -> erased
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_402 v19 v21 v22 v24 v25
                      -> erased
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_368 v8 v10 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'eff'45'app'45'infer_368 v18 v20 v21 v23
                      -> case coe v3 of
                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v24 v25 v26
                             -> let v27
                                      = coe
                                          du_agree'45'ii_340 (coe v0) (coe v15)
                                          (coe
                                             MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v8)
                                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                                          (coe
                                             MAlonzo.Code.Once.Type.C_ν'45'type_130 (coe v18)
                                             (coe MAlonzo.Code.Once.Type.C_eff_36))
                                          (coe v13) (coe v23) in
                                coe
                                  (coe
                                     seq (coe v27)
                                     (coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                           _ -> erased
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_402 v19 v21 v22 v24 v25
                      -> erased
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_386 v9 v11 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_386 v22 v24 v25 v26 v28 v29
                      -> let v30
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v17)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                      (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v22)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v24)
                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                      (coe v3))
                                   (coe v15) (coe v28) in
                         coe
                           (coe
                              seq (coe v30)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_418 v22 v24 v25 v27 v28
                      -> let v29
                               = coe
                                   du_agree'45'di_406 (coe v0) (coe v17) (coe v3)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                      (coe v2))
                                   (coe v24) (coe v12) (coe v28) (coe v15) in
                         coe
                           (case coe v29 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                -> case coe v31 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                       -> case coe v33 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                              -> case coe v35 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                     -> coe
                                                          seq (coe v36)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             erased erased)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_402 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v18 v19 v20
                      -> case coe v5 of
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_402 v24 v26 v27 v29 v30
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v31 v32 v33
                                    -> let v34
                                             = coe
                                                 du_agree'45'ii_340 (coe v0) (coe v16)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                    (coe v9)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                    (coe v20))
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                    (coe v24)
                                                    (coe
                                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                       (coe MAlonzo.Code.Once.Type.C_eff_36))
                                                    (coe v33))
                                                 (coe v14) (coe v29) in
                                       coe
                                         (coe
                                            seq (coe v34)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_418 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_386 v21 v23 v24 v25 v27 v28
                      -> let v29
                               = coe
                                   du_agree'45'di_406 (coe v0) (coe v16) (coe v2)
                                   (coe
                                      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v21)
                                      (coe
                                         MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v23)
                                         (coe MAlonzo.Code.Once.Type.C_pure_34))
                                      (coe v3))
                                   (coe v11) (coe v24) (coe v15) (coe v27) in
                         coe
                           (case coe v29 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                -> case coe v31 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                       -> case coe v33 of
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                              -> case coe v35 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                     -> coe
                                                          seq (coe v36)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             erased erased)
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError)
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'spine_418 v21 v23 v24 v26 v27
                      -> let v28
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v17) (coe v9) (coe v21)
                                   (coe v14) (coe v26) in
                         coe
                           (coe
                              seq (coe v28)
                              (let v29
                                     = coe
                                         du_agree'45'dd_424 (coe v0) (coe v16) (coe v9) (coe v2)
                                         (coe v3) (coe v11) (coe v23) (coe v15) (coe v27) in
                               coe
                                 (coe
                                    seq (coe v29)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'void_426 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg'45'void_426 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 du_agree'45'ii_340 (coe v0) (coe v11)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v9) (coe v15)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'void_454 v12 v13 v14 v15 v17 v18 v19 v20 v21
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v22 v23 v24 v25 v26
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'void_454 v33 v34 v35 v36 v38 v39 v40 v41 v42
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 du_agree'45'ii_340 (coe v0) (coe v22)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v19) (coe v40)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'l_470 v10 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'l_470 v22 v24 v25 v26
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 du_agree'45'ii_340 (coe v0) (coe v16)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v13) (coe v25)))
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486 v22 v23 v24 v25 v27
                      -> let v28
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v22) (coe v13)
                                   (coe v25) in
                         coe
                           (coe
                              seq (coe v28) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486 v10 v11 v12 v13 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v16 v17 v18
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'l_470 v23 v25 v26 v27
                      -> let v28
                               = coe
                                   du_agree'45'ii_340 (coe v0) (coe v17) (coe v10)
                                   (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v13) (coe v26) in
                         coe
                           (coe
                              seq (coe v28) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12))
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'void'45'r_486 v23 v24 v25 v26 v28
                      -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app'45'void_494 v8 v9
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app'45'void_502 v8 v9
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'void_510 v8 v9
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'Out'45'app'45'void_518 v8 v9
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'void_532 v9 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v5 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app'45'void_532 v20 v22 v24 v25
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 du_agree'45'ii_340 (coe v0) (coe v15)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120)
                                 (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v13) (coe v24)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeAgreement.agree-cc
d_agree'45'cc_352 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'cc_352 = erased
-- Once.TypeCheck.ModeAgreement.agree-ic
d_agree'45'ic_366 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ic_366 = erased
-- Once.TypeCheck.ModeAgreement.agree-dc
d_agree'45'dc_384 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'dc_384 = erased
-- Once.TypeCheck.ModeAgreement.agree-di
d_agree'45'di_406 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree'45'di_406 v0 v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_agree'45'di_406 v0 v1 v3 v4 v6 v7 v8 v9
du_agree'45'di_406 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree'45'di_406 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v11 v14 v16 v17 v18
        -> let v19
                 = coe
                     du_agree'45'ii_340 (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v14))
                        (coe v2))
                     (coe v3) (coe v16) (coe v7) in
           coe
             (coe
                seq (coe v19)
                (coe
                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                   (coe
                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                      (coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                         (coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v18) erased)))))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898 v12 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_906
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_916
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_926
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_934
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_940
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992 v13 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst'45'void_998
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd'45'void_1004
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022 v11 v12 v14 v15 v16 v17
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata'45'void_1032 v10 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeAgreement.agree-dd
d_agree'45'dd_424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree'45'dd_424 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_agree'45'dd_424 v0 v1 v2 v3 v4 v6 v7 v8 v9
du_agree'45'dd_424 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree'45'dd_424 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v12 v15 v17 v18 v19
        -> let v20
                 = coe
                     du_agree'45'di_406 (coe v0) (coe v1) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v12)
                        (coe
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v15))
                        (coe v3))
                     (coe v6) (coe v5) (coe v8) (coe v17) in
           coe
             (case coe v20 of
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v21 v22
                  -> case coe v22 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                         -> case coe v24 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                -> coe
                                     seq (coe v26)
                                     (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> MAlonzo.RTE.mazUnreachableError)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_878 v14 v18
        -> let v19
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v22 v25 v27 v28 v29
                       -> let v30
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v22)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v25))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_878 v14 v18)
                                    (coe v27) in
                          coe
                            (case coe v30 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                 -> case coe v32 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                        -> case coe v34 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                               -> coe
                                                    seq (coe v36)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v20 v21
                  -> case coe v8 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v25 v28 v30 v31 v32
                         -> let v33
                                  = coe
                                      du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v25)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v28))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_878 v14
                                         v18)
                                      (coe v30) in
                            coe
                              (case coe v33 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                   -> case coe v35 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                          -> case coe v37 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                 -> coe
                                                      seq (coe v39)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_878 v27 v31
                         -> let v32
                                  = coe
                                      du_agree'45'ii_340
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_362
                                         (coe v0) (coe v20) (coe v2))
                                      (coe v21) (coe v3) (coe v4) (coe v18) (coe v31) in
                            coe
                              (coe
                                 seq (coe v32)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v19)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898 v13 v16 v17 v18 v19
        -> let v20
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v23 v26 v28 v29 v30
                       -> let v31
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v23)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898 v13
                                       v16 v17 v18 v19)
                                    (coe v28) in
                          coe
                            (case coe v31 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                 -> case coe v33 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                        -> case coe v35 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                               -> coe
                                                    seq (coe v37)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                  -> let v23
                           = case coe v8 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v26 v29 v31 v32 v33
                                 -> let v34
                                          = coe
                                              du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                 (coe v26)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v29))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898
                                                 v13 v16 v17 v18 v19)
                                              (coe v31) in
                                    coe
                                      (case coe v34 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                           -> case coe v36 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                  -> case coe v38 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                         -> coe
                                                              seq (coe v40)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 erased erased)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v21 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
                            -> case coe v8 of
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v29 v32 v34 v35 v36
                                   -> let v37
                                            = coe
                                                du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v32))
                                                   (coe v4))
                                                (coe v5) (coe v6)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898
                                                   v13 v16 v17 v18 v19)
                                                (coe v34) in
                                      coe
                                        (case coe v37 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                             -> case coe v39 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                    -> case coe v41 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                           -> coe
                                                                seq (coe v43)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased erased)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_898 v30 v33 v34 v35 v36
                                   -> let v37
                                            = coe
                                                du_agree'45'dd_424 (coe v0) (coe v22) (coe v2)
                                                (coe v13) (coe v30) (coe v17) (coe v34) (coe v18)
                                                (coe v35) in
                                      coe
                                        (coe
                                           seq (coe v37)
                                           (let v38
                                                  = coe
                                                      du_agree'45'dd_424 (coe v0) (coe v25)
                                                      (coe v13) (coe v3) (coe v4) (coe v16)
                                                      (coe v33) (coe v19) (coe v36) in
                                            coe
                                              (coe
                                                 seq (coe v38)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    erased erased))))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v23)
                _ -> coe v20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_906
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v15 v18 v20 v21 v22
               -> let v23
                        = coe
                            du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v18))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_906)
                            (coe v20) in
                  coe
                    (case coe v23 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                         -> case coe v25 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                -> case coe v27 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                       -> coe
                                            seq (coe v29)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_906
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_916
        -> let v13
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v16 v19 v21 v22 v23
                       -> let v24
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v16)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_916)
                                    (coe v21) in
                          coe
                            (case coe v24 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                 -> case coe v26 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                        -> case coe v28 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                               -> coe
                                                    seq (coe v30)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__122 v14 v15
                  -> case coe v8 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v19 v22 v24 v25 v26
                         -> let v27
                                  = coe
                                      du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v19)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_916)
                                      (coe v24) in
                            coe
                              (case coe v27 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                   -> case coe v29 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                          -> case coe v31 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                 -> coe
                                                      seq (coe v33)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_916
                         -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v13)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_926
        -> let v13
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v16 v19 v21 v22 v23
                       -> let v24
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v16)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v19))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_926)
                                    (coe v21) in
                          coe
                            (case coe v24 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                 -> case coe v26 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                        -> case coe v28 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                               -> coe
                                                    seq (coe v30)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__122 v14 v15
                  -> case coe v8 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v19 v22 v24 v25 v26
                         -> let v27
                                  = coe
                                      du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v19)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_926)
                                      (coe v24) in
                            coe
                              (case coe v27 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                   -> case coe v29 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                          -> case coe v31 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                                 -> coe
                                                      seq (coe v33)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_926
                         -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v13)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_934
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v15 v18 v20 v21 v22
               -> let v23
                        = coe
                            du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v18))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_934)
                            (coe v20) in
                  coe
                    (case coe v23 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v24 v25
                         -> case coe v25 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                -> case coe v27 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                       -> coe
                                            seq (coe v29)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_934
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_940
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v14 v17 v19 v20 v21
               -> let v22
                        = coe
                            du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v17))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_940)
                            (coe v19) in
                  coe
                    (case coe v22 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                         -> case coe v24 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                -> case coe v26 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                       -> coe
                                            seq (coe v28)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_940
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960 v16 v17 v18 v19
        -> let v20
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v23 v26 v28 v29 v30
                       -> let v31
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v23)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960 v16 v17
                                       v18 v19)
                                    (coe v28) in
                          coe
                            (case coe v31 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                 -> case coe v33 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                        -> case coe v35 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                               -> coe
                                                    seq (coe v37)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                  -> let v23
                           = case coe v8 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v26 v29 v31 v32 v33
                                 -> let v34
                                          = coe
                                              du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                 (coe v26)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v29))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960
                                                 v16 v17 v18 v19)
                                              (coe v31) in
                                    coe
                                      (case coe v34 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                           -> case coe v36 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                  -> case coe v38 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                         -> coe
                                                              seq (coe v40)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 erased erased)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v21 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
                            -> let v26
                                     = case coe v8 of
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v29 v32 v34 v35 v36
                                           -> let v37
                                                    = coe
                                                        du_agree'45'di_406 (coe v0) (coe v1)
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                           (coe v29)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                              (coe v32))
                                                           (coe v4))
                                                        (coe v5) (coe v6)
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960
                                                           v16 v17 v18 v19)
                                                        (coe v34) in
                                              coe
                                                (case coe v37 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                     -> case coe v39 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                            -> case coe v41 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                   -> coe
                                                                        seq (coe v43)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           erased erased)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v2 of
                                    MAlonzo.Code.Once.Type.C__'43'__124 v27 v28
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v32 v35 v37 v38 v39
                                             -> let v40
                                                      = coe
                                                          du_agree'45'di_406 (coe v0) (coe v1)
                                                          (coe v3)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                             (coe v32)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe v35))
                                                             (coe v4))
                                                          (coe v5) (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960
                                                             v16 v17 v18 v19)
                                                          (coe v37) in
                                                coe
                                                  (case coe v40 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                       -> case coe v42 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                                              -> case coe v44 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v45 v46
                                                                     -> coe
                                                                          seq (coe v46)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             erased erased)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_960 v36 v37 v38 v39
                                             -> let v40
                                                      = coe
                                                          du_agree'45'dd_424 (coe v0) (coe v25)
                                                          (coe v27) (coe v3) (coe v4) (coe v16)
                                                          (coe v36) (coe v18) (coe v38) in
                                                coe
                                                  (let v41
                                                         = coe
                                                             du_agree'45'dd_424 (coe v0) (coe v22)
                                                             (coe v28) (coe v3) (coe v4) (coe v17)
                                                             (coe v37) (coe v19) (coe v39) in
                                                   coe
                                                     (coe
                                                        seq (coe v40)
                                                        (coe
                                                           seq (coe v41)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                              erased erased))))
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe v26)
                          _ -> coe v23)
                _ -> coe v20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980 v16 v17 v18 v19
        -> let v20
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v23 v26 v28 v29 v30
                       -> let v31
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v23)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v26))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980 v16 v17
                                       v18 v19)
                                    (coe v28) in
                          coe
                            (case coe v31 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                 -> case coe v33 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                        -> case coe v35 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                               -> coe
                                                    seq (coe v37)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v21 v22
                  -> let v23
                           = case coe v8 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v26 v29 v31 v32 v33
                                 -> let v34
                                          = coe
                                              du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                 (coe v26)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v29))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980
                                                 v16 v17 v18 v19)
                                              (coe v31) in
                                    coe
                                      (case coe v34 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                           -> case coe v36 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                  -> case coe v38 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                         -> coe
                                                              seq (coe v40)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 erased erased)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v21 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v24 v25
                            -> let v26
                                     = case coe v8 of
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v29 v32 v34 v35 v36
                                           -> let v37
                                                    = coe
                                                        du_agree'45'di_406 (coe v0) (coe v1)
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                           (coe v29)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                              (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                              (coe v32))
                                                           (coe v4))
                                                        (coe v5) (coe v6)
                                                        (coe
                                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980
                                                           v16 v17 v18 v19)
                                                        (coe v34) in
                                              coe
                                                (case coe v37 of
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                     -> case coe v39 of
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                                            -> case coe v41 of
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                                                   -> coe
                                                                        seq (coe v43)
                                                                        (coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           erased erased)
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError
                                                   _ -> MAlonzo.RTE.mazUnreachableError)
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v3 of
                                    MAlonzo.Code.Once.Type.C__'42'__122 v27 v28
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v32 v35 v37 v38 v39
                                             -> let v40
                                                      = coe
                                                          du_agree'45'di_406 (coe v0) (coe v1)
                                                          (coe v3)
                                                          (coe
                                                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                             (coe v32)
                                                             (coe
                                                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.C_Many_10)
                                                                (coe v35))
                                                             (coe v4))
                                                          (coe v5) (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980
                                                             v16 v17 v18 v19)
                                                          (coe v37) in
                                                coe
                                                  (case coe v40 of
                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                       -> case coe v42 of
                                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v43 v44
                                                              -> case coe v44 of
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v45 v46
                                                                     -> coe
                                                                          seq (coe v46)
                                                                          (coe
                                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                             erased erased)
                                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                                            _ -> MAlonzo.RTE.mazUnreachableError
                                                     _ -> MAlonzo.RTE.mazUnreachableError)
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_980 v36 v37 v38 v39
                                             -> case coe v4 of
                                                  MAlonzo.Code.Once.Type.C__'42'__122 v40 v41
                                                    -> let v42
                                                             = coe
                                                                 du_agree'45'dd_424 (coe v0)
                                                                 (coe v25) (coe v2) (coe v27)
                                                                 (coe v40) (coe v16) (coe v36)
                                                                 (coe v18) (coe v38) in
                                                       coe
                                                         (let v43
                                                                = coe
                                                                    du_agree'45'dd_424 (coe v0)
                                                                    (coe v22) (coe v2) (coe v28)
                                                                    (coe v41) (coe v17) (coe v37)
                                                                    (coe v19) (coe v39) in
                                                          coe
                                                            (coe
                                                               seq (coe v42)
                                                               (coe
                                                                  seq (coe v43)
                                                                  (coe
                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                     erased erased))))
                                                  _ -> coe v26
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe v26)
                          _ -> coe v23)
                _ -> coe v20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992 v14 v15
        -> let v16
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v19 v22 v24 v25 v26
                       -> let v27
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v19)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992 v14 v15)
                                    (coe v24) in
                          coe
                            (case coe v27 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                 -> case coe v29 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                        -> case coe v31 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                               -> coe
                                                    seq (coe v33)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                  -> let v19
                           = case coe v8 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v22 v25 v27 v28 v29
                                 -> let v30
                                          = coe
                                              du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                 (coe v22)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v25))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992
                                                 v14 v15)
                                              (coe v27) in
                                    coe
                                      (case coe v30 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                           -> case coe v32 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                  -> case coe v34 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                         -> coe
                                                              seq (coe v36)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 erased erased)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Once.Type.C_μ'45'type_128 v20
                            -> case coe v8 of
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v24 v27 v29 v30 v31
                                   -> let v32
                                            = coe
                                                du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                   (coe v24)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v27))
                                                   (coe v4))
                                                (coe v5) (coe v6)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992
                                                   v14 v15)
                                                (coe v29) in
                                      coe
                                        (case coe v32 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                             -> case coe v34 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                                    -> case coe v36 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                                           -> coe
                                                                seq (coe v38)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased erased)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_992 v26 v27
                                   -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v19)
                _ -> coe v16)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst'45'void_998
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v14 v17 v19 v20 v21
               -> let v22
                        = coe
                            du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v17))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst'45'void_998)
                            (coe v19) in
                  coe
                    (case coe v22 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                         -> case coe v24 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                -> case coe v26 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                       -> coe
                                            seq (coe v28)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst'45'void_998
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd'45'void_1004
        -> case coe v8 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v14 v17 v19 v20 v21
               -> let v22
                        = coe
                            du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v14)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v17))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd'45'void_1004)
                            (coe v19) in
                  coe
                    (case coe v22 of
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v23 v24
                         -> case coe v24 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v25 v26
                                -> case coe v26 of
                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v27 v28
                                       -> coe
                                            seq (coe v28)
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd'45'void_1004
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022 v12 v13 v15 v16 v17 v18
        -> let v19
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v22 v25 v27 v28 v29
                       -> let v30
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v22)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v25))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022
                                       v12 v13 v15 v16 v17 v18)
                                    (coe v27) in
                          coe
                            (case coe v30 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                 -> case coe v32 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                        -> case coe v34 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v35 v36
                                               -> coe
                                                    seq (coe v36)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v20 v21
                  -> let v22
                           = case coe v8 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v25 v28 v30 v31 v32
                                 -> let v33
                                          = coe
                                              du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                 (coe v25)
                                                 (coe
                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                    (coe v28))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022
                                                 v12 v13 v15 v16 v17 v18)
                                              (coe v30) in
                                    coe
                                      (case coe v33 of
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                           -> case coe v35 of
                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v36 v37
                                                  -> case coe v37 of
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v38 v39
                                                         -> coe
                                                              seq (coe v39)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 erased erased)
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v20 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v23 v24
                            -> case coe v8 of
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v28 v31 v33 v34 v35
                                   -> let v36
                                            = coe
                                                du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                   (coe v28)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                      (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                      (coe v31))
                                                   (coe v4))
                                                (coe v5) (coe v6)
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022
                                                   v12 v13 v15 v16 v17 v18)
                                                (coe v33) in
                                      coe
                                        (case coe v36 of
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v37 v38
                                             -> case coe v38 of
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v39 v40
                                                    -> case coe v40 of
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v41 v42
                                                           -> coe
                                                                seq (coe v42)
                                                                (coe
                                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                   erased erased)
                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                  _ -> MAlonzo.RTE.mazUnreachableError
                                           _ -> MAlonzo.RTE.mazUnreachableError)
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case'45'void_1022 v28 v29 v31 v32 v33 v34
                                   -> let v35
                                            = coe
                                                du_agree'45'dd_424 (coe v0) (coe v24)
                                                (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v12)
                                                (coe v28) (coe v15) (coe v31) (coe v17) (coe v33) in
                                      coe
                                        (let v36
                                               = coe
                                                   du_agree'45'dd_424 (coe v0) (coe v21)
                                                   (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v13)
                                                   (coe v29) (coe v16) (coe v32) (coe v18)
                                                   (coe v34) in
                                         coe
                                           (coe
                                              seq (coe v35)
                                              (coe
                                                 seq (coe v36)
                                                 (coe
                                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                    erased erased))))
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v22)
                _ -> coe v19)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata'45'void_1032 v11 v13
        -> let v14
                 = case coe v8 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v17 v20 v22 v23 v24
                       -> let v25
                                = coe
                                    du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v17)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata'45'void_1032
                                       v11 v13)
                                    (coe v22) in
                          coe
                            (case coe v25 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v26 v27
                                 -> case coe v27 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v28 v29
                                        -> case coe v29 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                               -> coe
                                                    seq (coe v31)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                  -> case coe v8 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_860 v20 v23 v25 v26 v27
                         -> let v28
                                  = coe
                                      du_agree'45'di_406 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v20)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata'45'void_1032
                                         v11 v13)
                                      (coe v25) in
                            coe
                              (case coe v28 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v29 v30
                                   -> case coe v30 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v31 v32
                                          -> case coe v32 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v33 v34
                                                 -> coe
                                                      seq (coe v34)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata'45'void_1032 v19 v21
                         -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v14)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeAgreement.mode-agree-ic
d_mode'45'agree'45'ic_2552 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mode'45'agree'45'ic_2552 = erased
-- Once.TypeCheck.ModeAgreement.mode-agree-dc
d_mode'45'agree'45'dc_2570 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_304 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mode'45'agree'45'dc_2570 = erased
