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

module MAlonzo.Code.Once.Adequacy.CataBridge where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Adequacy.CataRel
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Meaning
import qualified MAlonzo.Code.Once.Denotation.TraceDenote
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.CataBridge.base-refl
d_base'45'refl_12 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_148 ->
  AgdaAny -> AgdaAny
d_base'45'refl_12 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_150
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_154 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_156 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_158 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_160 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_166 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe d_base'45'refl_12 (coe v7) (coe v5) (coe v9))
                           (coe d_base'45'refl_12 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_172 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe d_base'45'refl_12 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe d_base'45'refl_12 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge.cata-bridge
d_cata'45'bridge_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'bridge_64 v0 v1 v2 v3 v4 v5 v6 ~v7 ~v8 v9
  = du_cata'45'bridge_64 v0 v1 v2 v3 v4 v5 v6 v9
du_cata'45'bridge_64 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'bridge_64 v0 v1 v2 v3 v4 v5 v6 v7
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_38 (coe v0))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
                    (coe (\ v9 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                       (coe v0) (coe v2) (coe v8)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       v3
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.du_coerce'45'functor'8315''185''45'D_10
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_418 (coe v0)
                             (coe (\ v9 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                                (coe v0) (coe v2) (coe v8))))
                       v7)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (coe
                    MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
                    (coe v0) (coe v7) (coe v3)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                       (coe v0) (coe v2) (coe v8))))))
      (coe
         (\ v8 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
                    (coe (\ v9 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v9)))
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                       (coe v0) (coe v2) (coe v8)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_52
                       (MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1))
                       v1 v4
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.du_coerce'45'functor'8315''185''45'D_10
                          (coe v0)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_418 (coe v0)
                             (coe (\ v9 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                                (coe v0) (coe v2) (coe v8))))
                       v7)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (coe
                    MAlonzo.Code.Once.Denotation.DenotTrace.d_cata'45'ev'45'alg'7472'_64
                    (coe v0) (coe v1) (coe v7) (coe v4)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                       (coe v0) (coe v2) (coe v8))))))
      (coe du_algR'45'full_158 (coe v0) (coe v2) (coe v5) (coe v7))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_26
         (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v6))
-- Once.Adequacy.CataBridge._.RelC
d_RelC_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_RelC_86 = erased
-- Once.Adequacy.CataBridge._.layer-lemma
d_layer'45'lemma_100 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_layer'45'lemma_100 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 v8 v9 v10 v11
                     v12
  = du_layer'45'lemma_100 v8 v9 v10 v11 v12
du_layer'45'lemma_100 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_layer'45'lemma_100 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_192 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe
                       d_base'45'refl_12 (coe v7) (coe v6)
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_30 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_634
                             (coe v7) (coe v6) (coe v2))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_194 -> coe v4
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_200 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_layer'45'lemma_100 (coe v9) (coe v7) (coe v11) (coe v12)
                                  (coe v4)
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           _ -> MAlonzo.RTE.mazUnreachableError
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12
                           MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                             -> coe
                                  du_layer'45'lemma_100 (coe v10) (coe v8) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_206 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8855'__120 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v11 v12
                      -> case coe v3 of
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v13 v14
                             -> case coe v4 of
                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v15 v16
                                    -> coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                                         (coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  du_layer'45'lemma_100 (coe v9) (coe v7) (coe v11)
                                                  (coe v13) (coe v15)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  du_layer'45'lemma_100 (coe v10) (coe v8) (coe v12)
                                                  (coe v14) (coe v16))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge._.algR-full
d_algR'45'full_158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algR'45'full_158 v0 ~v1 v2 ~v3 ~v4 v5 ~v6 v7 v8 v9 v10
  = du_algR'45'full_158 v0 v2 v5 v7 v8 v9 v10
du_algR'45'full_158 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_188 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algR'45'full_158 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            v2
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.du_coerce'45'functor'8315''185''45'D_10
               (coe v0)
               (coe
                  MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_418 (coe v0)
                  (coe (\ v7 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
                  (coe
                     MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                     (coe v0) (coe v1) (coe v4))))
            (coe
               MAlonzo.Code.Once.Denotation.DenotTrace.du_coerce'45'functor'8315''185''45'D_10
               (coe v0)
               (coe
                  MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_418 (coe v0)
                  (coe (\ v7 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
                  (coe
                     MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_788
                     (coe v0) (coe v1) (coe v5))))
            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_layer'45'lemma_100 (coe v0) (coe v1) (coe v4) (coe v5)
                  (coe v6)))
            v3))
