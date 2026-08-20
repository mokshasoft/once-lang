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
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Adequacy.CataBridge._.RelT
d_RelT_10 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_RelT_10 = erased
-- Once.Adequacy.CataBridge._.RelV
d_RelV_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny -> ()
d_RelV_12 = erased
-- Once.Adequacy.CataBridge.base-refl
d_base'45'refl_24 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
d_base'45'refl_24 ~v0 v1 v2 v3 = du_base'45'refl_24 v1 v2 v3
du_base'45'refl_24 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_IsBaseType_200 ->
  AgdaAny -> AgdaAny
du_base'45'refl_24 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Int_206 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Float_208 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Str_210 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Buffer_212 -> erased
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Prod_218 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'42'__126 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v9 v10
                      -> coe
                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                           (coe du_base'45'refl_24 (coe v7) (coe v5) (coe v9))
                           (coe du_base'45'refl_24 (coe v8) (coe v6) (coe v10))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_base'45'Sum_224 v5 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'43'__128 v7 v8
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v9
                      -> coe du_base'45'refl_24 (coe v7) (coe v5) (coe v9)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v9
                      -> coe du_base'45'refl_24 (coe v8) (coe v6) (coe v9)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge.cata-bridge
d_cata'45'bridge_78 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'bridge_78 v0 v1 v2 v3 v4 v5 v6 v7 ~v8 ~v9 v10
  = du_cata'45'bridge_78 v0 v1 v2 v3 v4 v5 v6 v7 v10
du_cata'45'bridge_78 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'bridge_78 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Adequacy.CataRel.du_cataS'45'rel_94
      (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v1))
      (coe
         (\ v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v1)
                    (coe (\ v10 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                       (coe v1) (coe v3) (coe v9)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe
                       v4
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
                          (coe v1)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 (coe v1)
                             (coe (\ v10 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10)))
                             (coe
                                MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                                (coe v1) (coe v3) (coe v9))))
                       v8)))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (coe
                    MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
                    (coe v1) (coe v8) (coe v4)
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                       (coe v1) (coe v3) (coe v9))))))
      (coe
         (\ v9 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe
                 MAlonzo.Code.Data.List.Base.du__'43''43'__32
                 (coe
                    MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v1)
                    (coe (\ v10 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10)))
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                       (coe v1) (coe v3) (coe v9)))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (let v10
                           = MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                               (coe v0)
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38
                                  (coe
                                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1)
                                     (coe v2)))
                               (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2)) (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
                                  (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 (coe v1)
                                     (coe
                                        (\ v10 ->
                                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10)))
                                     (coe
                                        MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                                        (coe v1) (coe v3) (coe v9)))) in
                     coe (coe v10 v8))))
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                 (coe
                    MAlonzo.Code.Once.Denotation.Meaning.du_cata'45'ev'45'alg'7472''45'D_10
                    (coe v1) (coe v8)
                    (coe
                       MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_404 (coe v0)
                       (coe
                          MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v1) (coe v2))
                       (coe v2) (coe v5))
                    (coe
                       MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                       (coe v1) (coe v3) (coe v9))))))
      (coe du_algR'45'full_172 (coe v1) (coe v3) (coe v6) (coe v8))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v1)) (coe v7))
-- Once.Adequacy.CataBridge._.RelC
d_RelC_100 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14 -> ()
d_RelC_100 = erased
-- Once.Adequacy.CataBridge._.layer-lemma
d_layer'45'lemma_114 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_layer'45'lemma_114 ~v0 ~v1 ~v2 ~v3 ~v4 ~v5 ~v6 ~v7 ~v8 v9 v10 v11
                     v12 v13
  = du_layer'45'lemma_114 v9 v10 v11 v12 v13
du_layer'45'lemma_114 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_layer'45'lemma_114 v0 v1 v2 v3 v4
  = case coe v1 of
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'K_244 v6
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C_K_114 v7
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
                    (coe
                       du_base'45'refl_24 (coe v7) (coe v6)
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v7)
                          (coe
                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'base'45'to'45'full_636
                             (coe v7) (coe v6) (coe v2))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Id_246 -> coe v4
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Sum_252 v7 v8
        -> case coe v0 of
             MAlonzo.Code.Once.Type.C__'8853'__118 v9 v10
               -> case coe v2 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v11
                      -> case coe v3 of
                           MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                             -> coe
                                  du_layer'45'lemma_114 (coe v9) (coe v7) (coe v11) (coe v12)
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
                                  du_layer'45'lemma_114 (coe v10) (coe v8) (coe v11) (coe v12)
                                  (coe v4)
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Functor.Translate.C_wf'45'Prod_258 v7 v8
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
                                                  du_layer'45'lemma_114 (coe v9) (coe v7) (coe v11)
                                                  (coe v13) (coe v15)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  du_layer'45'lemma_114 (coe v10) (coe v8) (coe v12)
                                                  (coe v14) (coe v16))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Adequacy.CataBridge._.algR-full
d_algR'45'full_172 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Semantics.Functor.T_μS_182 ->
  (AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_algR'45'full_172 ~v0 v1 ~v2 v3 ~v4 ~v5 ~v6 v7 v8 v9 v10 v11
  = du_algR'45'full_172 v1 v3 v7 v8 v9 v10 v11
du_algR'45'full_172 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_240 ->
  (AgdaAny ->
   AgdaAny ->
   AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  Integer ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_algR'45'full_172 v0 v1 v2 v3 v4 v5 v6
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 erased
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            v2
            (coe
               MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
               (coe v0)
               (coe
                  MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 (coe v0)
                  (coe (\ v7 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
                  (coe
                     MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                     (coe v0) (coe v1) (coe v4))))
            (coe
               MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
               (coe v0)
               (coe
                  MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 (coe v0)
                  (coe (\ v7 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
                  (coe
                     MAlonzo.Code.Once.Semantics.Value.du_coerce'45'μ'45'out_790
                     (coe v0) (coe v1) (coe v5))))
            (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
               (coe
                  du_layer'45'lemma_114 (coe v0) (coe v1) (coe v4) (coe v5)
                  (coe v6)))
            v3))
