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

module MAlonzo.Code.Once.TypeCheck.ModeSub where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Primitive
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Irrelevant
import qualified MAlonzo.Code.Data.List.Relation.Unary.Any
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Type.Sub
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.ModeAgreement
import qualified MAlonzo.Code.Once.TypeCheck.Raw

-- Once.TypeCheck.ModeSub.just≢nothing
d_just'8802'nothing_12 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_just'8802'nothing_12 = erased
-- Once.TypeCheck.ModeSub.ex
d_ex_18 ::
  MAlonzo.Code.Agda.Primitive.T_Level_18 ->
  () ->
  AgdaAny ->
  (AgdaAny -> MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20) ->
  MAlonzo.Code.Data.Irrelevant.T_Irrelevant_20
d_ex_18 = erased
-- Once.TypeCheck.ModeSub.arrow-at
d_arrow'45'at_40 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668
d_arrow'45'at_40 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 ~v9
  = du_arrow'45'at_40 v8
du_arrow'45'at_40 ::
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668
du_arrow'45'at_40 v0 = coe v0
-- Once.TypeCheck.ModeSub.sub-cod
d_sub'45'cod_58 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Type.T_ArrowKind_40 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_sub'45'cod_58 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 = du_sub'45'cod_58 v6
du_sub'45'cod_58 ::
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_sub'45'cod_58 v0
  = case coe v0 of
      MAlonzo.Code.Once.Type.Sub.C_sub'45'arr_74 v8 v9 v10 -> coe v9
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.≡-sub
d_'8801''45'sub_66 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_'8801''45'sub_66 v0 ~v1 ~v2 = du_'8801''45'sub_66 v0
du_'8801''45'sub_66 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_'8801''45'sub_66 v0
  = coe MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v0)
-- Once.TypeCheck.ModeSub.sub-along
d_sub'45'along_76 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_sub'45'along_76 ~v0 ~v1 ~v2 ~v3 v4 v5 = du_sub'45'along_76 v4 v5
du_sub'45'along_76 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_sub'45'along_76 v0 v1 = coe seq (coe v0) (coe v1)
-- Once.TypeCheck.ModeSub.apply-sub
d_apply'45'sub_90 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  () ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_apply'45'sub_90 ~v0 ~v1 v2 ~v3 ~v4 v5 = du_apply'45'sub_90 v2 v5
du_apply'45'sub_90 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_apply'45'sub_90 v0 v1
  = coe
      seq (coe v1)
      (coe MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v0))
-- Once.TypeCheck.ModeSub.di-cod
d_di'45'cod_108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  (MAlonzo.Code.Once.Type.T_Type_108 ->
   MAlonzo.Code.Once.Type.T_Purity_32 -> ()) ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_di'45'cod_108 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 v6 v7
  = du_di'45'cod_108 v6 v7
du_di'45'cod_108 ::
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_di'45'cod_108 v0 v1
  = case coe v0 of
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v2 v3
        -> case coe v3 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe seq (coe v5) (coe du_sub'45'cod_58 (coe v1))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.poly-sub
d_poly'45'sub_152 ::
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.Type.T_PolyType_254 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  [MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14] ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.T_ArrowSchema_668 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34 ->
   MAlonzo.Code.Data.List.Relation.Unary.Any.T_Any_34) ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
   MAlonzo.Code.Once.Type.T_Type_108) ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_poly'45'sub_152 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 ~v10 ~v11
                  ~v12 ~v13 ~v14 ~v15 ~v16 ~v17 ~v18 ~v19
  = du_poly'45'sub_152 v9
du_poly'45'sub_152 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_poly'45'sub_152 v0 = coe du_'8801''45'sub_66 (coe v0)
-- Once.TypeCheck.ModeSub.ic-sub
d_ic'45'sub_178 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_ic'45'sub_178 v0 v1 v2 v3 ~v4 ~v5 v6 v7
  = du_ic'45'sub_178 v0 v1 v2 v3 v6 v7
du_ic'45'sub_178 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_ic'45'sub_178 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'morph'45'check_466
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'morph'45'check_476
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496 v10 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520 v10 v12 v14 v15 v16 v17 v18 v19
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560 v13 v14 v15 v16
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'curry'45'check_578 v14
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_592 v12 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'ana'45'check_606 v12 v13
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v8 v11 v12
        -> coe
             du_sub'45'along_76
             (coe
                MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'ii_444
                (coe v0) (coe v1) (coe v2) (coe v8) (coe v4) (coe v11))
             (coe v12)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_654 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v15 v16
               -> case coe v3 of
                    MAlonzo.Code.Once.Type.C__'42'__124 v17 v18
                      -> case coe v4 of
                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_130 v24 v25 v26 v27
                             -> case coe v2 of
                                  MAlonzo.Code.Once.Type.C__'42'__124 v28 v29
                                    -> coe
                                         MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84
                                         (coe
                                            du_ic'45'sub_178 (coe v0) (coe v15) (coe v28) (coe v17)
                                            (coe v26) (coe v13))
                                         (coe
                                            du_ic'45'sub_178 (coe v0) (coe v16) (coe v29) (coe v18)
                                            (coe v27) (coe v14))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_664 v9 v10 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_676 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> case coe v4 of
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_326 v16 v18 v19
                      -> coe
                           du_apply'45'sub_90 (coe v2)
                           (coe
                              MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'ii_444
                              (coe v0) (coe v13)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__124
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v16)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe v2))
                                 (coe v16))
                              (coe
                                 MAlonzo.Code.Once.Type.C__'42'__124
                                 (coe
                                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v8)
                                    (coe
                                       MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                       (coe MAlonzo.Code.Once.Type.C_Many_10)
                                       (coe MAlonzo.Code.Once.Type.C_pure_34))
                                    (coe v3))
                                 (coe v8))
                              (coe v19) (coe v11))
                    MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'eff'45'app'45'infer_338 v16 v18 v19
                      -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_688 v10 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_700 v10 v11
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_710 v9 v10
        -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_724 v9 v10 v11 v16
        -> coe
             seq (coe v4) (coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.dc-sub
d_dc'45'sub_196 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_dc'45'sub_196 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = case coe v8 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'infer_742 v13 v16 v18 v19 v20
        -> coe
             du_sub'45'cod_58
             (coe
                du_ic'45'sub_178 (coe v0) (coe v1)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v13)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v16))
                   (coe v3))
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v2)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50
                      (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                   (coe v4))
                (coe v18) (coe v9))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_766 v15 v16 v17 v18 v19 v20 v25 v26 v27 v28
        -> let v29
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v31 v34 v35
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v31) (coe v6) (coe v7)
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_766 v15 v16 v17
                                  v18 v19 v20 v25 v26 v27 v28)
                               (coe v34))
                            (coe v35)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v30
                  -> case coe v9 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v33 v36 v37
                         -> coe
                              du_di'45'cod_108
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                 (coe v0) (coe v1) (coe v3) (coe v33) (coe v6) (coe v7)
                                 (coe
                                    MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'poly_766 v15 v16 v17
                                    v18 v19 v20 v25 v26 v27 v28)
                                 (coe v36))
                              (coe v37)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_724 v34 v35 v36 v41
                         -> case coe v27 of
                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v42 v43
                                -> coe
                                     seq (coe v43)
                                     (case coe v41 of
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v44 v45
                                          -> coe seq (coe v45) (coe du_poly'45'sub_152 (coe v3))
                                        _ -> MAlonzo.RTE.mazUnreachableError)
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v29)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_784 v15 v19
        -> let v20
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v22 v25 v26
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v22) (coe v6) (coe v7)
                               (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_784 v15 v19)
                               (coe v25))
                            (coe v26)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v21 v22
                  -> case coe v9 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v25 v28 v29
                         -> coe
                              du_di'45'cod_108
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                 (coe v0) (coe v1) (coe v3) (coe v25) (coe v6) (coe v7)
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'lam_784 v15 v19)
                                 (coe v28))
                              (coe v29)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_638 v29 v33
                         -> coe
                              du_ic'45'sub_178
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_418 (coe v0)
                                 (coe v21) (coe v2))
                              (coe v22) (coe v3) (coe v4) (coe v19) (coe v33)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v20)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804 v14 v17 v18 v19 v20
        -> let v21
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v23 v26 v27
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v23) (coe v6) (coe v7)
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804 v14 v17
                                  v18 v19 v20)
                               (coe v26))
                            (coe v27)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                  -> let v24
                           = case coe v9 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v26 v29 v30
                                 -> coe
                                      du_di'45'cod_108
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                         (coe v0) (coe v1) (coe v3) (coe v26) (coe v6) (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804
                                            v14 v17 v18 v19 v20)
                                         (coe v29))
                                      (coe v30)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v22 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
                            -> case coe v9 of
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'g_496 v31 v34 v35 v36 v37
                                   -> coe
                                        du_cg'45'sub_216 (coe v0) (coe v26) (coe v14) (coe v3)
                                        (coe v4) (coe v5) (coe v17) (coe v34) (coe v20) (coe v37)
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'compose'45'check'45'f_520 v31 v33 v35 v36 v37 v38 v39 v40
                                   -> coe
                                        du_di'45'cod_108
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                           (coe v0) (coe v26) (coe v3)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                              (coe v31)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v35))
                                              (coe v33))
                                           (coe v17) (coe v36) (coe v20) (coe v38))
                                        (coe v39)
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v29 v32 v33
                                   -> coe
                                        du_di'45'cod_108
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                           (coe v0) (coe v1) (coe v3) (coe v29) (coe v6) (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'compose_804
                                              v14 v17 v18 v19 v20)
                                           (coe v32))
                                        (coe v33)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v24)
                _ -> coe v21)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_812
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'check_420
               -> coe MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v2)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v15 v18 v19
               -> coe
                    du_di'45'cod_108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                       (coe v0) (coe v1) (coe v3) (coe v15) (coe v6) (coe v7)
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'id_812) (coe v18))
                    (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_822
        -> let v14
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v16 v19 v20
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v16) (coe v6) (coe v7)
                               (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_822)
                               (coe v19))
                            (coe v20)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__124 v15 v16
                  -> case coe v9 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'check_430
                         -> coe MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v3)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v19 v22 v23
                         -> coe
                              du_di'45'cod_108
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                 (coe v0) (coe v1) (coe v3) (coe v19) (coe v6) (coe v7)
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'fst_822)
                                 (coe v22))
                              (coe v23)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v14)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_832
        -> let v14
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v16 v19 v20
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v16) (coe v6) (coe v7)
                               (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_832)
                               (coe v19))
                            (coe v20)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'42'__124 v15 v16
                  -> case coe v9 of
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'check_440
                         -> coe MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170 (coe v3)
                       MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v19 v22 v23
                         -> coe
                              du_di'45'cod_108
                              (coe
                                 MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                 (coe v0) (coe v1) (coe v3) (coe v19) (coe v6) (coe v7)
                                 (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'snd_832)
                                 (coe v22))
                              (coe v23)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v14)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_840
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'morph'45'check_448
               -> coe
                    MAlonzo.Code.Once.Type.Sub.d_'60''58''45'refl_170
                    (coe MAlonzo.Code.Once.Type.C_Unit_120)
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v15 v18 v19
               -> coe
                    du_di'45'cod_108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                       (coe v0) (coe v1) (coe v3) (coe v15) (coe v6) (coe v7)
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'terminal_840)
                       (coe v18))
                    (coe v19)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_846
        -> case coe v9 of
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'morph'45'check_456
               -> coe MAlonzo.Code.Once.Type.Sub.C_sub'45'void_52
             MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v14 v17 v18
               -> coe
                    du_di'45'cod_108
                    (coe
                       MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                       (coe v0) (coe v1) (coe v3) (coe v14) (coe v6) (coe v7)
                       (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'initial_846)
                       (coe v17))
                    (coe v18)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866 v17 v18 v19 v20
        -> let v21
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v23 v26 v27
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v23) (coe v6) (coe v7)
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866 v17 v18 v19
                                  v20)
                               (coe v26))
                            (coe v27)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                  -> let v24
                           = case coe v9 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v26 v29 v30
                                 -> coe
                                      du_di'45'cod_108
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                         (coe v0) (coe v1) (coe v3) (coe v26) (coe v6) (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866 v17
                                            v18 v19 v20)
                                         (coe v29))
                                      (coe v30)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v22 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
                            -> let v27
                                     = case coe v9 of
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v29 v32 v33
                                           -> coe
                                                du_di'45'cod_108
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                                   (coe v0) (coe v1) (coe v3) (coe v29) (coe v6)
                                                   (coe v7)
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866
                                                      v17 v18 v19 v20)
                                                   (coe v32))
                                                (coe v33)
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v2 of
                                    MAlonzo.Code.Once.Type.C__'43'__126 v28 v29
                                      -> case coe v9 of
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case'45'copair'45'check_540 v37 v38 v39 v40
                                             -> coe
                                                  d_dc'45'sub_196 (coe v0) (coe v26) (coe v28)
                                                  (coe v3) (coe v4) (coe v5) (coe v17) (coe v37)
                                                  (coe v19) (coe v39)
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v32 v35 v36
                                             -> coe
                                                  du_di'45'cod_108
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                                     (coe v0) (coe v1) (coe v3) (coe v32) (coe v6)
                                                     (coe v7)
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'case_866
                                                        v17 v18 v19 v20)
                                                     (coe v35))
                                                  (coe v36)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe v27)
                          _ -> coe v24)
                _ -> coe v21)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886 v17 v18 v19 v20
        -> let v21
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v23 v26 v27
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v23) (coe v6) (coe v7)
                               (coe
                                  MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886 v17 v18 v19
                                  v20)
                               (coe v26))
                            (coe v27)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v22 v23
                  -> let v24
                           = case coe v9 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v26 v29 v30
                                 -> coe
                                      du_di'45'cod_108
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                         (coe v0) (coe v1) (coe v3) (coe v26) (coe v6) (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886 v17
                                            v18 v19 v20)
                                         (coe v29))
                                      (coe v30)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v22 of
                          MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v25 v26
                            -> let v27
                                     = case coe v9 of
                                         MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v29 v32 v33
                                           -> coe
                                                du_di'45'cod_108
                                                (coe
                                                   MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                                   (coe v0) (coe v1) (coe v3) (coe v29) (coe v6)
                                                   (coe v7)
                                                   (coe
                                                      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886
                                                      v17 v18 v19 v20)
                                                   (coe v32))
                                                (coe v33)
                                         _ -> MAlonzo.RTE.mazUnreachableError in
                               coe
                                 (case coe v3 of
                                    MAlonzo.Code.Once.Type.C__'42'__124 v28 v29
                                      -> case coe v9 of
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'morph'45'check_560 v37 v38 v39 v40
                                             -> case coe v4 of
                                                  MAlonzo.Code.Once.Type.C__'42'__124 v41 v42
                                                    -> coe
                                                         MAlonzo.Code.Once.Type.Sub.C_sub'45'prod_84
                                                         (d_dc'45'sub_196
                                                            (coe v0) (coe v26) (coe v2) (coe v28)
                                                            (coe v41) (coe v5) (coe v17) (coe v37)
                                                            (coe v19) (coe v39))
                                                         (d_dc'45'sub_196
                                                            (coe v0) (coe v23) (coe v2) (coe v29)
                                                            (coe v42) (coe v5) (coe v18) (coe v38)
                                                            (coe v20) (coe v40))
                                                  _ -> coe v27
                                           MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v32 v35 v36
                                             -> coe
                                                  du_di'45'cod_108
                                                  (coe
                                                     MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                                     (coe v0) (coe v1) (coe v3) (coe v32) (coe v6)
                                                     (coe v7)
                                                     (coe
                                                        MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'pair_886
                                                        v17 v18 v19 v20)
                                                     (coe v35))
                                                  (coe v36)
                                           _ -> MAlonzo.RTE.mazUnreachableError
                                    _ -> coe v27)
                          _ -> coe v24)
                _ -> coe v21)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900 v16 v17
        -> let v18
                 = case coe v9 of
                     MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v20 v23 v24
                       -> coe
                            du_di'45'cod_108
                            (coe
                               MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                               (coe v0) (coe v1) (coe v3) (coe v20) (coe v6) (coe v7)
                               (coe MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900 v16 v17)
                               (coe v23))
                            (coe v24)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v19 v20
                  -> let v21
                           = case coe v9 of
                               MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v23 v26 v27
                                 -> coe
                                      du_di'45'cod_108
                                      (coe
                                         MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                         (coe v0) (coe v1) (coe v3) (coe v23) (coe v6) (coe v7)
                                         (coe
                                            MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900 v16
                                            v17)
                                         (coe v26))
                                      (coe v27)
                               _ -> MAlonzo.RTE.mazUnreachableError in
                     coe
                       (case coe v2 of
                          MAlonzo.Code.Once.Type.C_μ'45'type_130 v22
                            -> case coe v9 of
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'cata'45'check_592 v29 v30
                                   -> coe
                                        du_sub'45'cod_58
                                        (coe
                                           du_ic'45'sub_178 (coe v0) (coe v20)
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                              (coe
                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                 (coe v22) (coe v3))
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                              (coe v3))
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                              (coe
                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170
                                                 (coe v22) (coe v4))
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v5))
                                              (coe v4))
                                           (coe v17) (coe v30))
                                 MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'sub_618 v25 v28 v29
                                   -> coe
                                        du_di'45'cod_108
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.ModeAgreement.du_agree'45'di_510
                                           (coe v0) (coe v1) (coe v3) (coe v25) (coe v6) (coe v7)
                                           (coe
                                              MAlonzo.Code.Once.TypeCheck.Judgment.C_d'45'cata_900
                                              v16 v17)
                                           (coe v28))
                                        (coe v29)
                                 _ -> MAlonzo.RTE.mazUnreachableError
                          _ -> coe v21)
                _ -> coe v18)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.TypeCheck.ModeSub.cg-sub
d_cg'45'sub_216 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
d_cg'45'sub_216 v0 v1 v2 ~v3 v4 v5 v6 v7 v8 ~v9 v10 v11
  = du_cg'45'sub_216 v0 v1 v2 v4 v5 v6 v7 v8 v10 v11
du_cg'45'sub_216 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_378 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7496'_'8758'_'8658''91'_'93''8614'_'10814'__24 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__16 ->
  MAlonzo.Code.Once.Type.Sub.T__'60''58'__48
du_cg'45'sub_216 v0 v1 v2 v3 v4 v5 v6 v7 v8 v9
  = coe
      d_dc'45'sub_196 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe v5) (coe v6) (coe v7) (coe v8) (coe v9)
