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

module MAlonzo.Code.Once.Lang.Laws.ModeAgreement where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.All
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Syntax
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.Poly
import qualified MAlonzo.Code.Once.Lang.Typing
import qualified MAlonzo.Code.Once.Lang.Typing.Scope
import qualified MAlonzo.Code.Once.Spec.Name

-- Once.Lang.Laws.ModeAgreement.just≢nothing
d_just'8802'nothing_14 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_14 = erased
-- Once.Lang.Laws.ModeAgreement.cod-≡
d_cod'45''8801'_28 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_cod'45''8801'_28 = erased
-- Once.Lang.Laws.ModeAgreement.arith-not-cmp
d_arith'45'not'45'cmp_32 ::
  MAlonzo.Code.Once.Lang.Syntax.T_BinOp_6 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_arith'45'not'45'cmp_32 = erased
-- Once.Lang.Laws.ModeAgreement.extractGroundF-irr
d_extractGroundF'45'irr_40 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyFunctor_8 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractGroundF'45'irr_40 = erased
-- Once.Lang.Laws.ModeAgreement.extractGround-irr
d_extractGround'45'irr_48 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_extractGround'45'irr_48 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-id
d_noinf'45'id_176 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'id_176 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-fst
d_noinf'45'fst_186 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'fst_186 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-snd
d_noinf'45'snd_196 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'snd_196 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-terminal
d_noinf'45'terminal_206 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'terminal_206 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-initial
d_noinf'45'initial_216 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'initial_216 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-inl
d_noinf'45'inl_226 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inl_226 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-inr
d_noinf'45'inr_236 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inr_236 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-curry-app
d_noinf'45'curry'45'app_248 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'curry'45'app_248 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-cata-app
d_noinf'45'cata'45'app_258 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'cata'45'app_258 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-ana-app
d_noinf'45'ana'45'app_268 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'ana'45'app_268 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-In-app
d_noinf'45'In'45'app_278 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'In'45'app_278 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-inl-app
d_noinf'45'inl'45'app_288 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inl'45'app_288 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-inr-app
d_noinf'45'inr'45'app_298 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'inr'45'app_298 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-initial-app
d_noinf'45'initial'45'app_308 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'initial'45'app_308 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-compose
d_noinf'45'compose_320 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'compose_320 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-case
d_noinf'45'case_332 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'case_332 = erased
-- Once.Lang.Laws.ModeAgreement.noinf-pair
d_noinf'45'pair_344 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_noinf'45'pair_344 = erased
-- Once.Lang.Laws.ModeAgreement.⇒-parts
d_'8658''45'parts_358 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_ArrowKind_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'8658''45'parts_358 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6
  = du_'8658''45'parts_358
du_'8658''45'parts_358 :: MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'8658''45'parts_358
  = coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
-- Once.Lang.Laws.ModeAgreement.dpoly-det
d_dpoly'45'det_384 ::
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_PolyType_10 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  MAlonzo.Code.Once.Lang.Type.Poly.T_ArrowSchema_286 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Lang.Type.T_Type_8) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_dpoly'45'det_384 = erased
-- Once.Lang.Laws.ModeAgreement.agree-ii
d_agree'45'ii_494 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree'45'ii_494 v0 v1 v2 v3 ~v4 ~v5 v6 v7
  = du_agree'45'ii_494 v0 v1 v2 v3 v6 v7
du_agree'45'ii_494 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree'45'ii_494 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.Lang.Typing.C_t'45'int_30
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'float_42
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit_46
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v10 v12
               -> case coe v10 of
                    MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v15 v16
                      -> case coe v16 of
                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v19 v20
                             -> case coe v20 of
                                  MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v23 v24
                                    -> case coe v24 of
                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v27 v28
                                           -> case coe v28 of
                                                MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v31 v32
                                                  -> case coe v32 of
                                                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v35 v36
                                                         -> case coe v36 of
                                                              MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v39 v40
                                                                -> coe
                                                                     seq (coe v40)
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v10
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v16
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_96 v18
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_112 v15 v16 v17 v18 v22
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'qualified_72 v11
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v9 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RResolved_40 v12
               -> let v13
                        = case coe v5 of
                            MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v16 v18
                              -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                            MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v18
                              -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                            _ -> MAlonzo.RTE.mazUnreachableError in
                  coe
                    (case coe v9 of
                       MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v16 v17
                         -> let v18
                                  = case coe v5 of
                                      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v21 v23
                                        -> coe
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                             erased
                                      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v23
                                        -> case coe v12 of
                                             MAlonzo.Code.Once.Spec.Name.C_canonical_12 v24
                                               -> case coe v24 of
                                                    (:) v25 v26
                                                      -> coe
                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                    _ -> coe v13
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError in
                            coe
                              (case coe v17 of
                                 MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v21 v22
                                   -> let v23
                                            = case coe v5 of
                                                MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v26 v28
                                                  -> coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased
                                                MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v28
                                                  -> case coe v12 of
                                                       MAlonzo.Code.Once.Spec.Name.C_canonical_12 v29
                                                         -> case coe v29 of
                                                              (:) v30 v31
                                                                -> coe
                                                                     MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                              _ -> coe v18
                                                       _ -> MAlonzo.RTE.mazUnreachableError
                                                _ -> MAlonzo.RTE.mazUnreachableError in
                                      coe
                                        (case coe v22 of
                                           MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v26 v27
                                             -> let v28
                                                      = case coe v5 of
                                                          MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v31 v33
                                                            -> coe
                                                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                 erased erased
                                                          MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v33
                                                            -> case coe v12 of
                                                                 MAlonzo.Code.Once.Spec.Name.C_canonical_12 v34
                                                                   -> case coe v34 of
                                                                        (:) v35 v36
                                                                          -> coe
                                                                               MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                        _ -> coe v23
                                                                 _ -> MAlonzo.RTE.mazUnreachableError
                                                          _ -> MAlonzo.RTE.mazUnreachableError in
                                                coe
                                                  (case coe v27 of
                                                     MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v31 v32
                                                       -> let v33
                                                                = case coe v5 of
                                                                    MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v36 v38
                                                                      -> coe
                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                           erased erased
                                                                    MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v38
                                                                      -> case coe v12 of
                                                                           MAlonzo.Code.Once.Spec.Name.C_canonical_12 v39
                                                                             -> case coe v39 of
                                                                                  (:) v40 v41
                                                                                    -> coe
                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                  _ -> coe v28
                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                    _ -> MAlonzo.RTE.mazUnreachableError in
                                                          coe
                                                            (case coe v32 of
                                                               MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v36 v37
                                                                 -> let v38
                                                                          = case coe v5 of
                                                                              MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v41 v43
                                                                                -> coe
                                                                                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                     erased erased
                                                                              MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v43
                                                                                -> case coe v12 of
                                                                                     MAlonzo.Code.Once.Spec.Name.C_canonical_12 v44
                                                                                       -> case coe
                                                                                                 v44 of
                                                                                            (:) v45 v46
                                                                                              -> coe
                                                                                                   MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                            _ -> coe
                                                                                                   v33
                                                                                     _ -> MAlonzo.RTE.mazUnreachableError
                                                                              _ -> MAlonzo.RTE.mazUnreachableError in
                                                                    coe
                                                                      (case coe v37 of
                                                                         MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v41 v42
                                                                           -> let v43
                                                                                    = case coe v5 of
                                                                                        MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v46 v48
                                                                                          -> coe
                                                                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                               erased
                                                                                               erased
                                                                                        MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v48
                                                                                          -> case coe
                                                                                                    v12 of
                                                                                               MAlonzo.Code.Once.Spec.Name.C_canonical_12 v49
                                                                                                 -> case coe
                                                                                                           v49 of
                                                                                                      (:) v50 v51
                                                                                                        -> coe
                                                                                                             MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                      _ -> coe
                                                                                                             v38
                                                                                               _ -> MAlonzo.RTE.mazUnreachableError
                                                                                        _ -> MAlonzo.RTE.mazUnreachableError in
                                                                              coe
                                                                                (case coe v42 of
                                                                                   MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v46 v47
                                                                                     -> let v48
                                                                                              = case coe
                                                                                                       v5 of
                                                                                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v51 v53
                                                                                                    -> coe
                                                                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                         erased
                                                                                                         erased
                                                                                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v53
                                                                                                    -> case coe
                                                                                                              v12 of
                                                                                                         MAlonzo.Code.Once.Spec.Name.C_canonical_12 v54
                                                                                                           -> case coe
                                                                                                                     v54 of
                                                                                                                (:) v55 v56
                                                                                                                  -> coe
                                                                                                                       MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                _ -> coe
                                                                                                                       v43
                                                                                                         _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                  _ -> MAlonzo.RTE.mazUnreachableError in
                                                                                        coe
                                                                                          (case coe
                                                                                                  v47 of
                                                                                             MAlonzo.Code.Data.List.Relation.Unary.All.C__'8759'__60 v51 v52
                                                                                               -> case coe
                                                                                                         v5 of
                                                                                                    MAlonzo.Code.Once.Lang.Typing.C_t'45'unit'45'var_50
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                    MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v56 v58
                                                                                                      -> coe
                                                                                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                                                           erased
                                                                                                           erased
                                                                                                    MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v58
                                                                                                      -> case coe
                                                                                                                v12 of
                                                                                                           MAlonzo.Code.Once.Spec.Name.C_canonical_12 v59
                                                                                                             -> case coe
                                                                                                                       v59 of
                                                                                                                  (:) v60 v61
                                                                                                                    -> coe
                                                                                                                         MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                                                                                                                  _ -> coe
                                                                                                                         v48
                                                                                                           _ -> MAlonzo.RTE.mazUnreachableError
                                                                                                    _ -> MAlonzo.RTE.mazUnreachableError
                                                                                             _ -> coe
                                                                                                    v48)
                                                                                   _ -> coe v43)
                                                                         _ -> coe v38)
                                                               _ -> coe v33)
                                                     _ -> coe v28)
                                           _ -> coe v23)
                                 _ -> coe v18)
                       _ -> coe v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v11
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'resolved_80 v15 v17
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'own_88 v17
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_96 v12
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v17
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_96 v19
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_112 v16 v17 v18 v19 v23
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_112 v9 v10 v11 v12 v16
        -> case coe v5 of
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'local_62 v22
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'import_96 v24
               -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
             MAlonzo.Code.Once.Lang.Typing.C_t'45'var'45'poly'45'instantiate'45'infer_112 v21 v22 v23 v24 v28
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'annot_122 v10 v11
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_138 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RPair_48 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v17 v18
                      -> case coe v5 of
                           MAlonzo.Code.Once.Lang.Typing.C_t'45'pair_138 v24 v25 v26 v27
                             -> case coe v3 of
                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 v28 v29
                                    -> let v30
                                             = coe
                                                 du_agree'45'ii_494 (coe v0) (coe v15) (coe v17)
                                                 (coe v28) (coe v13) (coe v26) in
                                       coe
                                         (let v31
                                                = coe
                                                    du_agree'45'ii_494 (coe v0) (coe v16) (coe v18)
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_146 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RUnaryOp_64 v11
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'neg_146 v15
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                           (coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                              (coe
                                 du_agree'45'ii_494 (coe v0) (coe v11)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v9) (coe v15)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'neg'45'float_158
        -> coe
             seq (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased)
      MAlonzo.Code.Once.Lang.Typing.C_t'45'let_178 v10 v12 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RLet_46 v17 v18 v19
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'let_178 v24 v26 v27 v28 v29 v30
                      -> let v31
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v18) (coe v10) (coe v24)
                                   (coe v15) (coe v29) in
                         coe
                           (coe
                              seq (coe v31)
                              (let v32
                                     = coe
                                         du_agree'45'ii_494
                                         (coe
                                            MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                            (coe
                                               addInt (coe (1 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22
                                                  (coe v17) (coe v10)
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                               (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                  (coe v0))
                                               v10
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128
                                               (coe v0)))
                                         (coe v19) (coe v2) (coe v3) (coe v16) (coe v30) in
                               coe
                                 (coe
                                    seq (coe v32)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'case_208 v12 v13 v15 v16 v17 v18 v19 v20 v21 v22
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RDestruct_50 v23 v24 v25 v26 v27
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'case_208 v34 v35 v37 v38 v39 v40 v41 v42 v43 v44
                      -> let v45
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v23)
                                   (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v12) (coe v13))
                                   (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v34) (coe v35))
                                   (coe v20) (coe v42) in
                         coe
                           (coe
                              seq (coe v45)
                              (let v46
                                     = coe
                                         du_agree'45'ii_494
                                         (coe
                                            MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                            (coe
                                               addInt (coe (1 :: Integer))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22
                                                  (coe v24) (coe v12)
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120
                                                  (coe v0)))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                               (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                  (coe v0))
                                               v12
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126
                                               (coe v0))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128
                                               (coe v0)))
                                         (coe v25) (coe v2) (coe v3) (coe v21) (coe v43) in
                               coe
                                 (let v47
                                        = coe
                                            du_agree'45'ii_494
                                            (coe
                                               MAlonzo.Code.Once.Lang.Typing.Scope.C_mkCtx_130
                                               (coe
                                                  addInt (coe (1 :: Integer))
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Typing.Scope.d_size_118
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Typing.Scope.C_mkBinding_22
                                                     (coe v26) (coe v13)
                                                     (coe
                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                                  (coe
                                                     MAlonzo.Code.Once.Lang.Typing.Scope.d_named_120
                                                     (coe v0)))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12
                                                  (MAlonzo.Code.Once.Lang.Typing.Scope.d_debruijn_122
                                                     (coe v0))
                                                  v13
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_imports_124
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_polys_126
                                                  (coe v0))
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Typing.Scope.d_sig_128
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_222 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_222 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_494 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14)
                                      (coe v26) in
                            coe
                              (coe
                                 seq (coe v27)
                                 (coe
                                    seq (coe v28)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_278 v22 v23 v25 v26
                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_236 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float_236 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13)
                                   (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_494 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14)
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_250 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'il_250 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_494 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v14)
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_264 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith'45'float'45'ir_264 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v13)
                                   (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_494 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14)
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_278 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RBinOp_62 v15 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'arith_222 v22 v23 v25 v26
                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'binop'45'cmp_278 v22 v23 v25 v26
                      -> let v27
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v16)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                   (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v13) (coe v25) in
                         coe
                           (let v28
                                  = coe
                                      du_agree'45'ii_494 (coe v0) (coe v17)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                      (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v14)
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_288 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'id'45'app_288 v16 v17
                      -> let v18
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v12) (coe v2) (coe v3) (coe v10)
                                   (coe v17) in
                         coe
                           (coe
                              seq (coe v18)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_300 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'fst'45'app_300 v17 v18 v19
                      -> let v20
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v13)
                                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v9))
                                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v3) (coe v17))
                                   (coe v11) (coe v19) in
                         coe
                           (coe
                              seq (coe v20)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_312 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'snd'45'app_312 v16 v18 v19
                      -> let v20
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v13)
                                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v8) (coe v2))
                                   (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v16) (coe v3))
                                   (coe v11) (coe v19) in
                         coe
                           (coe
                              seq (coe v20)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_322 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'terminal'45'app_322 v15 v16 v17
                      -> let v18
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v12) (coe v8) (coe v15)
                                   (coe v10) (coe v17) in
                         coe
                           (coe
                              seq (coe v18)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_334 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v12 v13
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'app'45'infer_334 v16 v18 v19
                      -> let v20
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v13)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v8)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                         (coe v2))
                                      (coe v8))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v16)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                         (coe v3))
                                      (coe v16))
                                   (coe v11) (coe v19) in
                         coe
                           (coe
                              seq (coe v20)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_350 v8 v10 v12 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
                      -> case coe v17 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v19 v20
                             -> coe
                                  seq (coe v12)
                                  (case coe v5 of
                                     MAlonzo.Code.Once.Lang.Typing.C_t'45'apply'45'eff'45'app'45'infer_350 v23 v25 v27 v28
                                       -> case coe v3 of
                                            MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v29 v30 v31
                                              -> case coe v30 of
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v32 v33
                                                     -> let v34
                                                              = coe
                                                                  du_agree'45'ii_494 (coe v0)
                                                                  (coe v15)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                        (coe v8)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                           (coe v20))
                                                                        (coe v18))
                                                                     (coe v8))
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                        (coe v23)
                                                                        (coe
                                                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                                           (coe
                                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                           (coe v33))
                                                                        (coe v31))
                                                                     (coe v23))
                                                                  (coe v13) (coe v28) in
                                                        coe
                                                          (coe
                                                             seq (coe v34)
                                                             (coe
                                                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                erased erased))
                                                   _ -> MAlonzo.RTE.mazUnreachableError
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_362 v8 v10 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v14 v15
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_362 v18 v20 v21 v23
                      -> let v24
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v15)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v8)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 (coe v18)
                                      (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                   (coe v13) (coe v23) in
                         coe
                           (coe
                              seq (coe v24)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_378 v18 v20 v22 v23 v25
                      -> erased
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_416 v19 v21 v22 v24 v26 v27
                      -> erased
                    _ -> erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_378 v8 v10 v12 v13 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v18 v19 v20
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v21 v22
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'app'45'infer_362 v25 v27 v28 v30
                                    -> erased
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'Out'45'eff'45'app'45'infer_378 v25 v27 v29 v30 v32
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v33 v34 v35
                                           -> case coe v34 of
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v36 v37
                                                  -> let v38
                                                           = coe
                                                               du_agree'45'ii_494 (coe v0) (coe v17)
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32
                                                                  (coe v8) (coe v22))
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32
                                                                  (coe v25) (coe v37))
                                                               (coe v15) (coe v32) in
                                                     coe
                                                       (coe
                                                          seq (coe v38)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             erased erased))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> erased
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_416 v26 v28 v29 v31 v33 v34
                                    -> erased
                                  _ -> erased
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app_396 v9 v11 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v17 v18
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app_396 v22 v24 v25 v26 v28 v29
                      -> let v30
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v17)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v11)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                      (coe v2))
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v22)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v24)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                                      (coe v3))
                                   (coe v15) (coe v28) in
                         coe
                           (coe
                              seq (coe v30)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_432 v22 v24 v25 v27 v28
                      -> let v29
                               = coe
                                   du_agree'45'di_560 (coe v0) (coe v17) (coe v3)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v11)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
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
      MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_416 v9 v11 v12 v14 v16 v17
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v18 v19
               -> case coe v2 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v20 v21 v22
                      -> case coe v21 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v23 v24
                             -> case coe v5 of
                                  MAlonzo.Code.Once.Lang.Typing.C_t'45'effApp_416 v28 v30 v31 v33 v35 v36
                                    -> case coe v3 of
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v37 v38 v39
                                           -> case coe v38 of
                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v40 v41
                                                  -> let v42
                                                           = coe
                                                               du_agree'45'ii_494 (coe v0) (coe v18)
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                  (coe v9)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                     (coe v24))
                                                                  (coe v22))
                                                               (coe
                                                                  MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                                  (coe v28)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                                     (coe
                                                                        MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                     (coe v41))
                                                                  (coe v39))
                                                               (coe v16) (coe v35) in
                                                     coe
                                                       (coe
                                                          seq (coe v42)
                                                          (coe
                                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                             erased erased))
                                                _ -> MAlonzo.RTE.mazUnreachableError
                                         _ -> MAlonzo.RTE.mazUnreachableError
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_432 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v16 v17
               -> case coe v5 of
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app_396 v21 v23 v24 v25 v27 v28
                      -> let v29
                               = coe
                                   du_agree'45'di_560 (coe v0) (coe v16) (coe v2)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v23)
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
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
                    MAlonzo.Code.Once.Lang.Typing.C_t'45'app'45'spine_432 v21 v23 v24 v26 v27
                      -> let v28
                               = coe
                                   du_agree'45'ii_494 (coe v0) (coe v17) (coe v9) (coe v21)
                                   (coe v14) (coe v26) in
                         coe
                           (coe
                              seq (coe v28)
                              (let v29
                                     = coe
                                         du_agree'45'dd_578 (coe v0) (coe v16) (coe v9) (coe v2)
                                         (coe v3) (coe v11) (coe v23) (coe v15) (coe v27) in
                               coe
                                 (coe
                                    seq (coe v29)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Laws.ModeAgreement.agree-cc
d_agree'45'cc_506 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'cc_506 = erased
-- Once.Lang.Laws.ModeAgreement.agree-ic
d_agree'45'ic_520 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'ic_520 = erased
-- Once.Lang.Laws.ModeAgreement.agree-dc
d_agree'45'dc_538 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_agree'45'dc_538 = erased
-- Once.Lang.Laws.ModeAgreement.agree-di
d_agree'45'di_560 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree'45'di_560 v0 v1 ~v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_agree'45'di_560 v0 v1 v3 v4 v6 v7 v8 v9
du_agree'45'di_560 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree'45'di_560 v0 v1 v2 v3 v4 v5 v6 v7
  = case coe v6 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v11 v14 v16 v17 v18
        -> let v19
                 = coe
                     du_agree'45'ii_494 (coe v0) (coe v1)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v14))
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_810 v13 v14 v15 v16 v17 v18 v23 v24 v25 v26
        -> coe
             seq (coe v7) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_850 v12 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_860 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_872 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_884 v12
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_894 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_902 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_922 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_942 v15 v16 v17 v18
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_958 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Laws.ModeAgreement.agree-dd
d_agree'45'dd_578 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_agree'45'dd_578 v0 v1 v2 v3 v4 ~v5 v6 v7 v8 v9
  = du_agree'45'dd_578 v0 v1 v2 v3 v4 v6 v7 v8 v9
du_agree'45'dd_578 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_agree'45'dd_578 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = case coe v7 of
      MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v12 v15 v17 v18 v19
        -> let v20
                 = coe
                     du_agree'45'di_560 (coe v0) (coe v1) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v12)
                        (coe
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v15))
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_810 v14 v15 v16 v17 v18 v19 v24 v25 v26 v27
        -> let v28
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v31 v34 v36 v37 v38
                       -> let v39
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v31)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v34))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_810 v14 v15 v16 v17
                                       v18 v19 v24 v25 v26 v27)
                                    (coe v36) in
                          coe
                            (case coe v39 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v40 v41
                                 -> case coe v41 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                        -> case coe v43 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                               -> coe
                                                    seq (coe v45)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RVar_36 v29
                  -> case coe v8 of
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v33 v36 v38 v39 v40
                         -> let v41
                                  = coe
                                      du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v33)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v36))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_810 v14 v15 v16
                                         v17 v18 v19 v24 v25 v26 v27)
                                      (coe v38) in
                            coe
                              (case coe v41 of
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                   -> case coe v43 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                          -> case coe v45 of
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v46 v47
                                                 -> coe
                                                      seq (coe v47)
                                                      (coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         erased erased)
                                               _ -> MAlonzo.RTE.mazUnreachableError
                                        _ -> MAlonzo.RTE.mazUnreachableError
                                 _ -> MAlonzo.RTE.mazUnreachableError)
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'poly_810 v35 v36 v37 v38 v39 v40 v45 v46 v47 v48
                         -> case coe v26 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v49 v50
                                -> coe
                                     seq (coe v50)
                                     (case coe v47 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v51 v52
                                          -> coe
                                               seq (coe v52)
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                                  erased)
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v28)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_830 v14 v17 v18
        -> let v19
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v22 v25 v27 v28 v29
                       -> let v30
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v22)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v25))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_830 v14 v17 v18)
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
                MAlonzo.Code.Once.Lang.Syntax.C_RLam_44 v20 v21
                  -> case coe v8 of
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v25 v28 v30 v31 v32
                         -> let v33
                                  = coe
                                      du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v25)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v28))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_830 v14 v17 v18)
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
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'lam_830 v27 v30 v31
                         -> let v32
                                  = coe
                                      du_agree'45'ii_494
                                      (coe
                                         MAlonzo.Code.Once.Lang.Typing.Scope.d_extendNamedCtx_132
                                         (coe v0) (coe v20) (coe v2))
                                      (coe v21) (coe v3) (coe v4) (coe v18) (coe v31) in
                            coe
                              (coe
                                 seq (coe v32)
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased))
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v19)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_850 v13 v16 v17 v18 v19
        -> let v20
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v23 v26 v28 v29 v30
                       -> let v31
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v23)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v26))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_850 v13 v16 v17
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
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
                  -> let v23
                           = case coe v8 of
                               MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v26 v29 v31 v32 v33
                                 -> let v34
                                          = coe
                                              du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                 (coe v26)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe v29))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_850
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
                          MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
                            -> case coe v8 of
                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v29 v32 v34 v35 v36
                                   -> let v37
                                            = coe
                                                du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                   (coe v29)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                      (coe v32))
                                                   (coe v4))
                                                (coe v5) (coe v6)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_850
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
                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'compose_850 v30 v33 v34 v35 v36
                                   -> let v37
                                            = coe
                                                du_agree'45'dd_578 (coe v0) (coe v22) (coe v2)
                                                (coe v13) (coe v30) (coe v17) (coe v34) (coe v18)
                                                (coe v35) in
                                      coe
                                        (coe
                                           seq (coe v37)
                                           (let v38
                                                  = coe
                                                      du_agree'45'dd_578 (coe v0) (coe v25)
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'id_860 v12
        -> case coe v8 of
             MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v16 v19 v21 v22 v23
               -> let v24
                        = coe
                            du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v19))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'id_860 v12) (coe v21) in
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
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Lang.Typing.C_d'45'id_860 v16
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_872 v13
        -> let v14
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v17 v20 v22 v23 v24
                       -> let v25
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v17)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v20))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_872 v13)
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
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.C__'42'__24 v15 v16
                  -> case coe v8 of
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v20 v23 v25 v26 v27
                         -> let v28
                                  = coe
                                      du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v20)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v23))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_872 v13)
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
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'fst_872 v21
                         -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v14)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_884 v13
        -> let v14
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v17 v20 v22 v23 v24
                       -> let v25
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v17)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v20))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_884 v13)
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
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.C__'42'__24 v15 v16
                  -> case coe v8 of
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v20 v23 v25 v26 v27
                         -> let v28
                                  = coe
                                      du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v20)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v23))
                                         (coe v4))
                                      (coe v5) (coe v6)
                                      (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_884 v13)
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
                       MAlonzo.Code.Once.Lang.Typing.C_d'45'snd_884 v21
                         -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v14)
      MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_894 v12
        -> case coe v8 of
             MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v16 v19 v21 v22 v23
               -> let v24
                        = coe
                            du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v19))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_894 v12)
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
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                               erased)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError)
             MAlonzo.Code.Once.Lang.Typing.C_d'45'terminal_894 v16
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_902 v11
        -> case coe v8 of
             MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v15 v18 v20 v21 v22
               -> let v23
                        = coe
                            du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                            (coe
                               MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v15)
                               (coe
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v18))
                               (coe v4))
                            (coe v5) (coe v6)
                            (coe MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_902 v11)
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
             MAlonzo.Code.Once.Lang.Typing.C_d'45'initial_902 v14
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Lang.Typing.C_d'45'case_922 v16 v17 v18 v19
        -> let v20
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v23 v26 v28 v29 v30
                       -> let v31
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v23)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v26))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Typing.C_d'45'case_922 v16 v17 v18
                                       v19)
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
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
                  -> let v23
                           = case coe v8 of
                               MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v26 v29 v31 v32 v33
                                 -> let v34
                                          = coe
                                              du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                 (coe v26)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe v29))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'case_922 v16
                                                 v17 v18 v19)
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
                          MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
                            -> let v26
                                     = case coe v8 of
                                         MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v29 v32 v34 v35 v36
                                           -> let v37
                                                    = coe
                                                        du_agree'45'di_560 (coe v0) (coe v1)
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                           (coe v29)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                              (coe v32))
                                                           (coe v4))
                                                        (coe v5) (coe v6)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'case_922
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
                                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v27 v28
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v32 v35 v37 v38 v39
                                             -> let v40
                                                      = coe
                                                          du_agree'45'di_560 (coe v0) (coe v1)
                                                          (coe v3)
                                                          (coe
                                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                             (coe v32)
                                                             (coe
                                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                (coe v35))
                                                             (coe v4))
                                                          (coe v5) (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.Lang.Typing.C_d'45'case_922
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
                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'case_922 v36 v37 v38 v39
                                             -> let v40
                                                      = coe
                                                          du_agree'45'dd_578 (coe v0) (coe v25)
                                                          (coe v27) (coe v3) (coe v4) (coe v16)
                                                          (coe v36) (coe v18) (coe v38) in
                                                coe
                                                  (let v41
                                                         = coe
                                                             du_agree'45'dd_578 (coe v0) (coe v22)
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_942 v16 v17 v18 v19
        -> let v20
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v23 v26 v28 v29 v30
                       -> let v31
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v23)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v26))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_942 v16 v17 v18
                                       v19)
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
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v21 v22
                  -> let v23
                           = case coe v8 of
                               MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v26 v29 v31 v32 v33
                                 -> let v34
                                          = coe
                                              du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                 (coe v26)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe v29))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_942 v16
                                                 v17 v18 v19)
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
                          MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v24 v25
                            -> let v26
                                     = case coe v8 of
                                         MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v29 v32 v34 v35 v36
                                           -> let v37
                                                    = coe
                                                        du_agree'45'di_560 (coe v0) (coe v1)
                                                        (coe v3)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                           (coe v29)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                              (coe
                                                                 MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                              (coe v32))
                                                           (coe v4))
                                                        (coe v5) (coe v6)
                                                        (coe
                                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_942
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
                                    MAlonzo.Code.Once.Lang.Type.C__'42'__24 v27 v28
                                      -> case coe v8 of
                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v32 v35 v37 v38 v39
                                             -> let v40
                                                      = coe
                                                          du_agree'45'di_560 (coe v0) (coe v1)
                                                          (coe v3)
                                                          (coe
                                                             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                             (coe v32)
                                                             (coe
                                                                MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                                (coe
                                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                                (coe v35))
                                                             (coe v4))
                                                          (coe v5) (coe v6)
                                                          (coe
                                                             MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_942
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
                                           MAlonzo.Code.Once.Lang.Typing.C_d'45'pair_942 v36 v37 v38 v39
                                             -> case coe v4 of
                                                  MAlonzo.Code.Once.Lang.Type.C__'42'__24 v40 v41
                                                    -> let v42
                                                             = coe
                                                                 du_agree'45'dd_578 (coe v0)
                                                                 (coe v25) (coe v2) (coe v27)
                                                                 (coe v40) (coe v16) (coe v36)
                                                                 (coe v18) (coe v38) in
                                                       coe
                                                         (let v43
                                                                = coe
                                                                    du_agree'45'dd_578 (coe v0)
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
      MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_958 v14 v15 v16 v17
        -> let v18
                 = case coe v8 of
                     MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v21 v24 v26 v27 v28
                       -> let v29
                                = coe
                                    du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v21)
                                       (coe
                                          MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                          (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                          (coe v24))
                                       (coe v4))
                                    (coe v5) (coe v6)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_958 v14 v15 v16
                                       v17)
                                    (coe v26) in
                          coe
                            (case coe v29 of
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v30 v31
                                 -> case coe v31 of
                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v32 v33
                                        -> case coe v33 of
                                             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v34 v35
                                               -> coe
                                                    seq (coe v35)
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       erased erased)
                                             _ -> MAlonzo.RTE.mazUnreachableError
                                      _ -> MAlonzo.RTE.mazUnreachableError
                               _ -> MAlonzo.RTE.mazUnreachableError)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Lang.Syntax.C_RApp_42 v19 v20
                  -> let v21
                           = case coe v8 of
                               MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v24 v27 v29 v30 v31
                                 -> let v32
                                          = coe
                                              du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                 (coe v24)
                                                 (coe
                                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                    (coe
                                                       MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                    (coe v27))
                                                 (coe v4))
                                              (coe v5) (coe v6)
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_958 v14
                                                 v15 v16 v17)
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
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v22
                            -> case coe v8 of
                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'infer_786 v26 v29 v31 v32 v33
                                   -> let v34
                                            = coe
                                                du_agree'45'di_560 (coe v0) (coe v1) (coe v3)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                   (coe v26)
                                                   (coe
                                                      MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                      (coe v29))
                                                   (coe v4))
                                                (coe v5) (coe v6)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_958 v14
                                                   v15 v16 v17)
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
                                 MAlonzo.Code.Once.Lang.Typing.C_d'45'cata_958 v28 v29 v30 v31
                                   -> coe MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased erased
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v21)
                _ -> coe v18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Lang.Laws.ModeAgreement.mode-agree-ic
d_mode'45'agree'45'ic_2282 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mode'45'agree'45'ic_2282 = erased
-- Once.Lang.Laws.ModeAgreement.mode-agree-dc
d_mode'45'agree'45'dc_2300 ::
  MAlonzo.Code.Once.Lang.Typing.Scope.T_NamedCtx_104 ->
  MAlonzo.Code.Once.Lang.Syntax.T_RawExpr_34 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.Grade.T_Purity_32 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.Lang.Typing.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12
d_mode'45'agree'45'dc_2300 = erased
