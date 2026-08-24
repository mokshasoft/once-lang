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

module MAlonzo.Code.Once.Denotation.Meaning where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.String.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.TraceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Dyadic
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.TypeCheck.Classify
import qualified MAlonzo.Code.Once.TypeCheck.Judgment
import qualified MAlonzo.Code.Once.TypeCheck.Raw
import qualified MAlonzo.Code.Once.Word

-- Once.Denotation.Meaning.cata-ev-algᴰ-D
d_cata'45'ev'45'alg'7472''45'D_10 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg'7472''45'D_10 v0 ~v1 v2 v3 v4
  = du_cata'45'ev'45'alg'7472''45'D_10 v0 v2 v3 v4
du_cata'45'ev'45'alg'7472''45'D_10 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  Integer ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'ev'45'alg'7472''45'D_10 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
            (coe (\ v4 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
            (coe v3))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
            (coe v2 (coe du_z_26 (coe v0) (coe v3))) (coe v1)))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
         (coe v2 (coe du_z_26 (coe v0) (coe v3))) (coe v1))
-- Once.Denotation.Meaning._.z
d_z_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny
d_z_26 v0 ~v1 ~v2 ~v3 v4 = du_z_26 v0 v4
du_z_26 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_z_26 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Denotation.Meaning.cata-sem
d_cata'45'sem_32 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'sem_32 v0 ~v1 v2 v3 v4 v5
  = du_cata'45'sem_32 v0 v2 v3 v4 v5
du_cata'45'sem_32 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'sem_32 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942 v0 v1
      (coe du_cata'45'ev'45'alg'7472''45'D_10 (coe v0) (coe v4) (coe v2))
      (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v3))
-- Once.Denotation.Meaning.in-value
d_in'45'value_50 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  AgdaAny -> MAlonzo.Code.Once.Semantics.Functor.T_μS_182
d_in'45'value_50 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_sem'45'In_922 (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 (coe v0)
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
            (coe
               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0)
               (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)))
            (coe v1)))
-- Once.Denotation.Meaning.named-sem
d_named'45'sem_60 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_named'45'sem_60 v0 v1 v2 v3 v4 v5 v6 ~v7
  = du_named'45'sem_60 v0 v1 v2 v3 v4 v5 v6
du_named'45'sem_60 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_named'45'sem_60 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158 (coe v0)
         (coe
            MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_370 (coe v0)
            (coe v1) (coe v3) (coe v4) (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56 (coe v0)
            (coe v6)))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v1)
         (coe
            MAlonzo.Code.Once.SigOp.Info.du_semM_188
            (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_370
               (coe v0) (coe v1) (coe v3) (coe v4) (coe v5))
            v2
            (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
               (coe v0) (coe v6))))
-- Once.Denotation.Meaning.⟦_⟧ᵍ
d_'10214'_'10215''7501'_84 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> AgdaAny
d_'10214'_'10215''7501'_84 ~v0 v1 v2 v3 v4
  = du_'10214'_'10215''7501'_84 v1 v2 v3 v4
du_'10214'_'10215''7501'_84 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7501'_'8758'__14 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 -> AgdaAny
du_'10214'_'10215''7501'_84 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'int_318
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v6
               -> coe
                    MAlonzo.Code.Once.Word.d_fromℤ_20
                    (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v3))
                    (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'float_330 v8 v9
        -> coe
             MAlonzo.Code.Once.Float.Dyadic.d_encode_140
             (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v3))
             (coe v8)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'terminal_334
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'pair_346 v9 v10
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v11 v12
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe
                              du_'10214'_'10215''7501'_84 (coe v11) (coe v13) (coe v9) (coe v3))
                           (coe
                              du_'10214'_'10215''7501'_84 (coe v12) (coe v14) (coe v10) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inl_356 v8
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                           (coe
                              du_'10214'_'10215''7501'_84 (coe v10) (coe v11) (coe v8) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'inr_366 v8
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v9 v10
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
                      -> coe
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                           (coe
                              du_'10214'_'10215''7501'_84 (coe v10) (coe v12) (coe v8) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_g'45'In_376 v7 v9
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v10 v11
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v12
                      -> coe
                           d_in'45'value_50 (coe v12)
                           (coe
                              du_'10214'_'10215''7501'_84 (coe v11)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v12) (coe v1))
                              (coe v9) (coe v3))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Meaning.⟦_⟧ᵐ
d_'10214'_'10215''7504'_124 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Purity_32 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''7504'_124 ~v0 v1 v2 ~v3 v4 v5 v6
  = du_'10214'_'10215''7504'_124 v1 v2 v4 v5 v6
du_'10214'_'10215''7504'_124 ::
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7504'_'8758'_'8680''91'_'93'__18 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214'_'10215''7504'_124 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'id_384
        -> coe
             (\ v10 v11 ->
                coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12 v10)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'fst_394
        -> coe
             (\ v11 v12 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v11)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'snd_404
        -> coe
             (\ v11 v12 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v11)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'terminal_412
        -> coe
             (\ v10 v11 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'initial_420
        -> coe (\ v10 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inl_430
        -> coe
             (\ v11 v12 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v11)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'inr_440
        -> coe
             (\ v11 v12 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v11)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'compose_456 v9 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
                      -> coe
                           (\ v19 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe du_'10214'_'10215''7504'_124 v16 v1 v9 v14 v4 v19)
                                (coe
                                   du_'10214'_'10215''7504'_124 (coe v18) (coe v9) (coe v2)
                                   (coe v13) (coe v4)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'case_472 v12 v13
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
                      -> case coe v1 of
                           MAlonzo.Code.Once.Type.C__'43'__128 v18 v19
                             -> coe
                                  MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                  (coe
                                     du_'10214'_'10215''7504'_124 (coe v17) (coe v18) (coe v2)
                                     (coe v12) (coe v4))
                                  (coe
                                     du_'10214'_'10215''7504'_124 (coe v15) (coe v19) (coe v2)
                                     (coe v13) (coe v4))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'pair_486 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v15 v16
                      -> case coe v2 of
                           MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                             -> coe
                                  (\ v19 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                       (coe du_'10214'_'10215''7504'_124 v16 v1 v17 v11 v4 v19)
                                       (coe
                                          (\ v20 ->
                                             coe
                                               MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                               (coe
                                                  du_'10214'_'10215''7504'_124 v14 v1 v18 v12 v4
                                                  v19)
                                               (coe
                                                  (\ v21 v22 ->
                                                     coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                       (coe
                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                          (coe v20) (coe v21)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'curry_498 v10
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
                      -> coe
                           (\ v16 v17 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                (coe
                                   (\ v18 ->
                                      coe
                                        du_'10214'_'10215''7504'_124 v12
                                        (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v13))
                                        v15 v10 v4
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                           (coe v18)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'cata_512 v10 v12
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v1 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v15
                      -> coe
                           du_cata'45'sem_32 (coe v15) (coe v10)
                           (coe
                              du_'10214'_'10215''7504'_124 (coe v14)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v15) (coe v2))
                              (coe v2) (coe v12) (coe v4))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'const_524 v10
        -> coe
             (\ v11 v12 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     du_'10214'_'10215''7501'_84 (coe v0) (coe v2) (coe v10) (coe v4)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named_536 v13 v14
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v15
               -> coe
                    (\ v16 v17 ->
                       coe
                         du_named'45'sem_60 (coe v1) (coe v2) (coe v4)
                         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v15)) (coe v13)
                         (coe v14) v16)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_m'45'named'45'resolved_548 v11 v12
        -> case coe v0 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v13
               -> coe
                    (\ v14 v15 ->
                       coe
                         du_named'45'sem_60 (coe v1) (coe v2) (coe v4) (coe v13) (coe v11)
                         (coe v12) v14)
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Meaning.lookupᴰ
d_lookup'7472'_232 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_lookup'7472'_232 ~v0 v1 v2 v3 = du_lookup'7472'_232 v1 v2 v3
du_lookup'7472'_232 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_lookup'7472'_232 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v4 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v8 v9 -> coe v9
                    _ -> MAlonzo.RTE.mazUnreachableError
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe du_lookup'7472'_232 (coe v4) (coe v8) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Meaning.svarᴰ
d_svar'7472'_264 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_184 -> AgdaAny -> AgdaAny
d_svar'7472'_264 ~v0 v1 ~v2 ~v3 v4 v5 = du_svar'7472'_264 v1 v4 v5
du_svar'7472'_264 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_SVar_184 -> AgdaAny -> AgdaAny
du_svar'7472'_264 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Surface.Context.C_svar_192 v5
        -> coe du_lookup'7472'_232 (coe v0) (coe v5) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Meaning.sigOpValᴰ
d_sigOpVal'7472'_274 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigOpVal'7472'_274 v0 v1 v2 ~v3 = du_sigOpVal'7472'_274 v0 v1 v2
du_sigOpVal'7472'_274 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_160 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_sigOpVal'7472'_274 v0 v1 v2
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
         (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v2)
         (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v0)
         (coe
            MAlonzo.Code.Once.SigOp.Info.du_semM_188 v2 v1
            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.Denotation.Meaning.sigOpRefᴰ
d_sigOpRef'7472'_284 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.CanonicalName.T_CanonicalName_4 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsConcrete_226 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_sigOpRef'7472'_284 v0 v1 v2 v3
  = case coe v3 of
      MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v5
        -> coe
             (\ v6 ->
                coe
                  du_sigOpVal'7472'_274 (coe v0) (coe v1)
                  (coe
                     MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_370
                     (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v0) (coe v2)
                     (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                     (coe MAlonzo.Code.Once.Functor.Translate.C_con'45'base_230 v5)))
      MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v13 v14 ->
                               coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe
                                    MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                                    (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_412
                                       (coe v9) (coe v11) (coe v10) (coe v2) (coe v7) (coe v8))
                                    (coe
                                       MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56 (coe v9)
                                       (coe v13)))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v11)
                                    (coe
                                       MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                       (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_412
                                          (coe v9) (coe v11) (coe v10) (coe v2) (coe v7) (coe v8))
                                       v1
                                       (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                          (coe v9) (coe v13)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Meaning.Env
d_Env_312 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 -> ()
d_Env_312 = erased
-- Once.Denotation.Meaning.⟦_⟧ᶜ
d_'10214'_'10215''7580'_324 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7580'_'8758'_'10814'__24 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''7580'_324 v0 v1 v2 v3 v4 v5 v6
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'morph'45'lift_560 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            du_'10214'_'10215''7504'_124 (coe v1) (coe v13) (coe v15) (coe v12)
                            (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'embed_570 v11
        -> coe d_'10214'_'10215''7522'_334 v0 v1 v2 v3 v11 v5 v6
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'lam_588 v13 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLam_44 v17 v18
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v19 v20 v21
                      -> coe
                           (\ v22 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                (coe
                                   (\ v23 ->
                                      d_'10214'_'10215''7580'_324
                                        (coe
                                           MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                           (coe v0) (coe v17) (coe v19))
                                        (coe v18) (coe v21)
                                        (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v13 v3)
                                        (coe v16) (coe v5)
                                        (coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v6)
                                           (coe v23)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'value'45'lift_600 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v17 v18 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                 (coe
                                    du_'10214'_'10215''7501'_84 (coe v1) (coe v15) (coe v12)
                                    (coe v5)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair'45'lit'45'check_616 v12 v13 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                           (coe
                              d_'10214'_'10215''7580'_324 (coe v0) (coe v16) (coe v18) (coe v12)
                              (coe v14) (coe v5) (coe v6))
                           (coe
                              (\ v20 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                   (coe
                                      d_'10214'_'10215''7580'_324 (coe v0) (coe v17) (coe v19)
                                      (coe v13) (coe v15) (coe v5) (coe v6))
                                   (coe
                                      (\ v21 v22 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                           (coe
                                              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v20)
                                              (coe v21))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'In'45'app'45'check_628 v10 v11 v13
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v14 v15
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v16
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                           (coe
                              d_'10214'_'10215''7580'_324 (coe v0) (coe v15)
                              (coe
                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v16) (coe v2))
                              (coe v11) (coe v13) (coe v5) (coe v6))
                           (coe
                              (\ v17 v18 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                   (coe d_in'45'value_50 (coe v16) (coe v17))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'check_640 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       d_'10214'_'10215''7522'_334 v0 v14
                       (coe
                          MAlonzo.Code.Once.Type.C__'42'__126
                          (coe
                             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                (coe MAlonzo.Code.Once.Type.C_Many_10)
                                (coe MAlonzo.Code.Once.Type.C_pure_34))
                             (coe v2))
                          (coe v9))
                       v11 v12 v5 v6)
                    (coe
                       (\ v15 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inl'45'app'45'check_652 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                           (coe
                              d_'10214'_'10215''7580'_324 (coe v0) (coe v14) (coe v15) (coe v11)
                              (coe v12) (coe v5) (coe v6))
                           (coe
                              (\ v17 v18 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v17))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'inr'45'app'45'check_664 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v13 v14
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'43'__128 v15 v16
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                           (coe
                              d_'10214'_'10215''7580'_324 (coe v0) (coe v14) (coe v16) (coe v11)
                              (coe v12) (coe v5) (coe v6))
                           (coe
                              (\ v17 v18 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                   (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v17))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'initial'45'app'45'check_674 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       d_'10214'_'10215''7580'_324 (coe v0) (coe v13)
                       (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v10) (coe v11)
                       (coe v5) (coe v6))
                    (\ v14 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'subsume_686 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    d_'10214'_'10215''7580'_324 (coe v0) (coe v1)
                    (coe
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v13)
                       (coe
                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                          (coe MAlonzo.Code.Once.Type.C_pure_34))
                       (coe v15))
                    (coe v3) (coe v12) (coe v5) (coe v6)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'arg'45'driven'45'app'45'check_702 v10 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       d_'10214'_'10215''7580'_324 (coe v0) (coe v17)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50
                             (coe MAlonzo.Code.Once.Type.C_Many_10)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v12) (coe v16) (coe v5) (coe v6))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                       (coe d_'10214'_'10215''7522'_334 v0 v18 v10 v13 v15 v5 v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate_716 v10 v11 v12 v19
        -> coe
             d_'10214'_'10215''7580'_324
             (coe
                MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                (coe v12))
             (coe v11) (coe v2)
             (coe
                MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                (coe
                   MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                   (coe
                      MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                      (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                      (coe v12))))
             (coe v19) (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.Meaning.⟦_⟧ᵢ
d_'10214'_'10215''7522'_334 ::
  MAlonzo.Code.Once.TypeCheck.Classify.T_NamedCtx_338 ->
  MAlonzo.Code.Once.TypeCheck.Raw.T_RawExpr_34 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.TypeCheck.Judgment.T__'8866''7522'_'8758'_'10814'__10 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''7522'_334 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'int_30
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RInt_54 v8
               -> coe
                    (\ v9 v10 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            MAlonzo.Code.Once.Word.d_fromℤ_20
                            (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v5))
                            (coe v8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'float_42 v10 v11
        -> coe
             (\ v12 v13 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Float.Dyadic.d_encode_140
                     (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v5))
                     (coe v10)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'str_48
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RStringLit_58 v8
               -> coe
                    (\ v9 v10 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            MAlonzo.Code.Once.SigOp.Info.du_semM_188
                            (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_356
                               (coe v8))
                            v5 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit_52
        -> coe
             (\ v7 v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'unit'45'var_56
        -> coe
             (\ v7 v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'local_68 v10
        -> coe
             (\ v13 v14 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     du_svar'7472'_264
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_debruijn_358 (coe v0))
                     (coe v10) (coe v13)))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'qualified_78 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RQualified_38 v12 v13
               -> coe
                    (\ v14 ->
                       d_sigOpRef'7472'_284
                         (coe v2) (coe v5)
                         (coe
                            MAlonzo.Code.Once.CanonicalName.d_bare_12
                            (coe
                               MAlonzo.Code.Data.String.Base.d__'43''43'__20 v13
                               (coe
                                  MAlonzo.Code.Data.String.Base.d__'43''43'__20
                                  ("." :: Data.Text.Text) v12)))
                         (coe v11))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'resolved_86 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RResolved_40 v11
               -> coe
                    (\ v12 ->
                       d_sigOpRef'7472'_284 (coe v2) (coe v5) (coe v11) (coe v10))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'import_94 v12
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RVar_36 v13
               -> coe
                    (\ v14 ->
                       d_sigOpRef'7472'_284
                         (coe v2) (coe v5)
                         (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v13))
                         (coe v12))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'var'45'poly'45'instantiate'45'infer_110 v9 v10 v11 v12 v20
        -> coe
             (\ v21 ->
                d_'10214'_'10215''7580'_324
                  (coe
                     MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                     (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                     (coe v11))
                  (coe v10) (coe v2)
                  (coe
                     MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70
                     (coe
                        MAlonzo.Code.Once.TypeCheck.Classify.d_size_354
                        (coe
                           MAlonzo.Code.Once.TypeCheck.Classify.d_ctxWithImportsAndPolys_376
                           (coe MAlonzo.Code.Once.TypeCheck.Classify.d_imports_362 (coe v0))
                           (coe v11))))
                  (coe v20) (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'annot_120 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RAnnot_60 v11 v12
               -> coe
                    (\ v13 ->
                       d_'10214'_'10215''7580'_324
                         (coe v0) (coe v11) (coe v2) (coe v3) (coe v10) (coe v5) (coe v13))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'pair_136 v11 v12 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RPair_48 v15 v16
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'42'__126 v17 v18
                      -> coe
                           (\ v19 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe d_'10214'_'10215''7522'_334 v0 v15 v17 v11 v13 v5 v19)
                                (coe
                                   (\ v20 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe d_'10214'_'10215''7522'_334 v0 v16 v18 v12 v14 v5 v19)
                                        (coe
                                           (\ v21 v22 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                   (coe v20) (coe v21)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'neg_144 v9
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RUnaryOp_64 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe
                            d_'10214'_'10215''7522'_334 v0 v11
                            (coe MAlonzo.Code.Once.Type.C_Int_136) v3 v9 v5 v12)
                         (coe
                            (\ v13 v14 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                 (coe
                                    MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                    MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_342 v5
                                    v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'let_164 v10 v12 v13 v14 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RLet_46 v17 v18 v19
               -> coe
                    (\ v20 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe d_'10214'_'10215''7522'_334 v0 v18 v10 v13 v15 v5 v20)
                         (coe
                            (\ v21 ->
                               coe
                                 d_'10214'_'10215''7522'_334
                                 (MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                    (coe v0) (coe v17) (coe v10))
                                 v19 v2
                                 (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v12 v14) v16
                                 v5
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v20)
                                    (coe v21)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'case_194 v12 v13 v15 v16 v17 v18 v19 v20 v21 v22
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RDestruct_50 v23 v24 v25 v26 v27
               -> coe
                    (\ v28 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe
                            d_'10214'_'10215''7522'_334 v0 v23
                            (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v12) (coe v13)) v17
                            v20 v5 v28)
                         (coe
                            MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                            (\ v29 ->
                               coe
                                 d_'10214'_'10215''7522'_334
                                 (MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                    (coe v0) (coe v24) (coe v12))
                                 v25 v2
                                 (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v15 v18) v21
                                 v5
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v28)
                                    (coe v29)))
                            (\ v29 ->
                               coe
                                 d_'10214'_'10215''7522'_334
                                 (MAlonzo.Code.Once.TypeCheck.Classify.d_extendNamedCtx_402
                                    (coe v0) (coe v26) (coe v13))
                                 v27 v2
                                 (coe MAlonzo.Code.Once.Surface.Context.C__'8759'__66 v16 v19) v22
                                 v5
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v28)
                                    (coe v29)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'arith_208 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpAdd_8
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_332
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpSub_10
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_334
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMul_12
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_336
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpDiv_14
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_338
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpMod_16
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_340
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'binop'45'cmp_222 v10 v11 v13 v14
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RBinOp_62 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLt_18
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_344
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpLe_20
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_346
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGt_22
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_348
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpGe_24
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_350
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpEq_26
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_352
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    MAlonzo.Code.Once.TypeCheck.Raw.C_OpNe_28
                      -> coe
                           (\ v18 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                (coe
                                   d_'10214'_'10215''7522'_334 v0 v16
                                   (coe MAlonzo.Code.Once.Type.C_Int_136) v10 v13 v5 v18)
                                (coe
                                   (\ v19 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v17
                                           (coe MAlonzo.Code.Once.Type.C_Int_136) v11 v14 v5 v18)
                                        (coe
                                           (\ v20 v21 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                (coe
                                                   MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                   MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_354
                                                   v5
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v19) (coe v20))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'id'45'app_232 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    (\ v13 -> coe d_'10214'_'10215''7522'_334 v0 v12 v2 v9 v10 v5 v13)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'fst'45'app_244 v9 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    (\ v14 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe
                            d_'10214'_'10215''7522'_334 v0 v13
                            (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v2) (coe v9)) v10 v11
                            v5 v14)
                         (coe
                            (\ v15 v16 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v15)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'snd'45'app_256 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    (\ v14 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe
                            d_'10214'_'10215''7522'_334 v0 v13
                            (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v8) (coe v2)) v10 v11
                            v5 v14)
                         (coe
                            (\ v15 v16 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'terminal'45'app_266 v8 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe d_'10214'_'10215''7522'_334 v0 v12 v8 v9 v10 v5 v13)
                         (coe
                            (\ v14 v15 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'apply'45'app'45'infer_278 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v12 v13
               -> coe
                    (\ v14 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe
                            d_'10214'_'10215''7522'_334 v0 v13
                            (coe
                               MAlonzo.Code.Once.Type.C__'42'__126
                               (coe
                                  MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                                  (coe
                                     MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                     (coe MAlonzo.Code.Once.Type.C_Many_10)
                                     (coe MAlonzo.Code.Once.Type.C_pure_34))
                                  (coe v2))
                               (coe v8))
                            v10 v11 v5 v14)
                         (coe
                            (\ v15 ->
                               coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v15
                                 (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v15)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'app_296 v9 v11 v12 v13 v15 v16
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v17 v18
               -> coe
                    (\ v19 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                         (coe
                            d_'10214'_'10215''7522'_334 v0 v17
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                                  (coe MAlonzo.Code.Once.Type.C_pure_34))
                               (coe v2))
                            v12 v15 v5 v19)
                         (coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                            (coe
                               d_'10214'_'10215''7580'_324 (coe v0) (coe v18) (coe v9) (coe v13)
                               (coe v16) (coe v5) (coe v19))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.TypeCheck.Judgment.C_t'45'effApp_312 v9 v11 v12 v14 v15
        -> case coe v1 of
             MAlonzo.Code.Once.TypeCheck.Raw.C_RApp_42 v16 v17
               -> case coe v2 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v18 v19 v20
                      -> coe
                           (\ v21 v22 ->
                              coe
                                MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                (coe
                                   (\ v23 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                        (coe
                                           d_'10214'_'10215''7522'_334 v0 v16
                                           (coe
                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                              (coe v9)
                                              (coe
                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                 (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                 (coe MAlonzo.Code.Once.Type.C_eff_36))
                                              (coe v20))
                                           v11 v14 v5 v21)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                           (coe
                                              d_'10214'_'10215''7580'_324 (coe v0) (coe v17)
                                              (coe v9) (coe v12) (coe v15) (coe v5) (coe v21))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
