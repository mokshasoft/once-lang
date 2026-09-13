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

module MAlonzo.Code.Once.Denotation.DenotPrefix where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Nat
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.DenotPrefix.Goodν
d_Goodν_10 a0 a1 = ()
data T_Goodν_10
  = C_constructor_34 MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_222
                     (Integer -> AgdaAny)
-- Once.Denotation.DenotPrefix.GoodLayer
d_GoodLayer_16 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 -> AgdaAny -> ()
d_GoodLayer_16 = erased
-- Once.Denotation.DenotPrefix.Goodν.force-pf
d_force'45'pf_28 ::
  T_Goodν_10 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_222
d_force'45'pf_28 v0
  = case coe v0 of
      C_constructor_34 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.Goodν.force-good
d_force'45'good_32 :: T_Goodν_10 -> Integer -> AgdaAny
d_force'45'good_32 v0
  = case coe v0 of
      C_constructor_34 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.Good
d_Good_74 :: MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> ()
d_Good_74 = erased
-- Once.Denotation.DenotPrefix.GoodT
d_GoodT_78 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) -> ()
d_GoodT_78 = erased
-- Once.Denotation.DenotPrefix.injectν-Good
d_injectν'45'Good_146 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> T_Goodν_10
d_injectν'45'Good_146 v0 v1
  = coe
      C_constructor_34
      (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
      (coe
         (\ v2 ->
            d_injectν'45'layer_154
              (coe v0) (coe v0)
              (coe MAlonzo.Code.Once.Semantics.Functor.d_unfoldS_204 (coe v1))))
-- Once.Denotation.DenotPrefix.injectν-layer
d_injectν'45'layer_154 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_injectν'45'layer_154 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_injectν'45'Good_146 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe d_injectν'45'layer_154 (coe v0) (coe v3) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe d_injectν'45'layer_154 (coe v0) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_injectν'45'layer_154 (coe v0) (coe v3) (coe v5))
                    (coe d_injectν'45'layer_154 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.inject-Good
d_inject'45'Good_204 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_inject'45'Good_204 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_inject'45'Good_204 (coe v2) (coe v4))
                    (coe d_inject'45'Good_204 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe d_inject'45'Good_204 (coe v2) (coe v4)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe d_inject'45'Good_204 (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v2 v3 v4
        -> case coe v3 of
             MAlonzo.Code.Once.Type.C_mk'45'kind_50 v5 v6
               -> case coe v5 of
                    MAlonzo.Code.Once.Type.C_Zero_6
                      -> coe
                           (\ v7 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                                (coe (\ v8 -> d_inject'45'Good_204 (coe v4) (coe v1 v7))))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v7 v8 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                                (coe
                                   (\ v9 ->
                                      d_inject'45'Good_204
                                        (coe v4)
                                        (coe
                                           v1
                                           (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_454
                                              (coe v2) (coe v7))))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v7 v8 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                                (coe
                                   (\ v9 ->
                                      d_inject'45'Good_204
                                        (coe v4)
                                        (coe
                                           v1
                                           (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_454
                                              (coe v2) (coe v7))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2
        -> coe
             d_injectν'45'Good_146
             (coe MAlonzo.Code.Once.Functor.Translate.du_translateF_60 (coe v2))
             (coe v1)
      MAlonzo.Code.Once.Type.C_Int_132
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Float_134
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Str_136
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_Buffer_138
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.evalᴰ-good-schemes
d_eval'7472''45'good'45'schemes_286
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.DenotPrefix.eval\7472-good-schemes"
-- Once.Denotation.DenotPrefix.evalᴰ-good
d_eval'7472''45'good_298 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval'7472''45'good_298 v0 v1 v2 v3 v4
  = let v5
          = \ v5 -> coe d_eval'7472''45'good'45'schemes_286 erased in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C_id_22
           -> coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                     (coe (\ v8 -> v7)))
         MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
           -> coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Denotation.TraceMonad.du_'62''62''61'T'45'pf_390
                        (coe
                           MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                           (coe v1) (coe v7) (coe v10) (coe v4))
                        (coe
                           MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                           (coe v7) (coe v2) (coe v9))
                        (coe
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                           (coe
                              du_ihf_406 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4)
                              (coe v11)))
                        (coe
                           (\ v12 ->
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                (coe
                                   d_ihg_410 (coe v0) (coe v1) (coe v2) (coe v7) (coe v9) (coe v10)
                                   (coe v4) (coe v11) (coe v12)))))
                     (coe
                        (\ v12 ->
                           coe
                             MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (d_ihg_410
                                (coe v0) (coe v1) (coe v2) (coe v7) (coe v9) (coe v10) (coe v4)
                                (coe v11) (coe v12))
                             (coe
                                MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v12
                                (coe
                                   MAlonzo.Code.Data.List.Base.du_length_268
                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                      (coe
                                         MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 v0
                                         v1 v7 v10 v4 v12)))))))
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
                  -> coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               MAlonzo.Code.Once.Denotation.TraceMonad.du_'62''62''61'T'45'pf_390
                               (coe
                                  MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                                  (coe v1) (coe v11) (coe v9) (coe v4))
                               (coe
                                  (\ v14 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                       (coe
                                          MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                                          (coe v0) (coe v1) (coe v12) (coe v10) (coe v4))
                                       (coe
                                          (\ v15 v16 ->
                                             coe
                                               MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe v14) (coe v15))))))
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                  (coe
                                     du_ihf_438 (coe v0) (coe v1) (coe v11) (coe v9) (coe v4)
                                     (coe v13)))
                               (coe
                                  (\ v14 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_'62''62''61'T'45'pf_390
                                       (coe
                                          MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                                          (coe v0) (coe v1) (coe v12) (coe v10) (coe v4))
                                       (coe
                                          (\ v15 v16 ->
                                             coe
                                               MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                                                        (coe v0) (coe v1) (coe v11) (coe v9)
                                                        (coe v4))
                                                     (coe v14))
                                                  (coe v15))))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                          (coe
                                             du_ihg_440 (coe v0) (coe v1) (coe v12) (coe v10)
                                             (coe v4) (coe v13)))
                                       (coe
                                          (\ v15 ->
                                             coe
                                               MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)))))
                            (coe
                               (\ v14 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_ihf_438 (coe v0) (coe v1) (coe v11) (coe v9) (coe v4)
                                          (coe v13))
                                       v14)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                       (coe
                                          du_ihg_440 (coe v0) (coe v1) (coe v12) (coe v10) (coe v4)
                                          (coe v13))
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Nat.d__'45'__22 v14
                                          (coe
                                             MAlonzo.Code.Data.List.Base.du_length_268
                                             (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                (coe
                                                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                                                   v0 v1 v11 v9 v4 v14))))))))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fst_44
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                            (coe
                               (\ v11 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_snd_50
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                            (coe
                               (\ v11 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10))))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inl_56
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                            (coe (\ v11 -> v10)))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inr_62
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                            (coe (\ v11 -> v10)))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_case_70 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
                  -> case coe v4 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                         -> coe (\ v14 -> coe d_eval'7472''45'good_298 v0 v11 v2 v9 v13 v14)
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                         -> coe
                              (\ v14 -> coe d_eval'7472''45'good_298 v0 v12 v2 v10 v13 v14)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_terminal_74
           -> coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                     (coe (\ v8 -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
         MAlonzo.Code.Once.IR.C_curry_86 v9
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                  -> coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_246)
                            (coe
                               (\ v13 v14 v15 ->
                                  coe
                                    d_eval'7472''45'good_298 v0
                                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v10)) v11
                                    v9
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                       (coe v14))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                       (coe v15)))))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_apply_92
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> case coe v8 of
                       MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                         -> coe
                              (\ v12 ->
                                 coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v12
                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                                   (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v12)))
                       _ -> coe v5
                _ -> coe v5
         _ -> coe v5)
-- Once.Denotation.DenotPrefix._.ihf
d_ihf_406 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihf_406 v0 v1 ~v2 v3 ~v4 v5 v6 v7 = du_ihf_406 v0 v1 v3 v5 v6 v7
du_ihf_406 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihf_406 v0 v1 v2 v3 v4 v5
  = coe d_eval'7472''45'good_298 v0 v1 v2 v3 v4 v5
-- Once.Denotation.DenotPrefix._.ihg
d_ihg_410 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihg_410 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      d_eval'7472''45'good_298 v0 v3 v2 v4
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_72
         (coe
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
            (coe v1) (coe v3) (coe v5) (coe v6))
         (coe v8))
      (coe
         MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_ihf_406 (coe v0) (coe v1) (coe v3) (coe v5) (coe v6) (coe v7))
         v8)
-- Once.Denotation.DenotPrefix._.ihf
d_ihf_438 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihf_438 v0 v1 v2 ~v3 v4 ~v5 v6 v7 = du_ihf_438 v0 v1 v2 v4 v6 v7
du_ihf_438 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihf_438 v0 v1 v2 v3 v4 v5
  = coe d_eval'7472''45'good_298 v0 v1 v2 v3 v4 v5
-- Once.Denotation.DenotPrefix._.ihg
d_ihg_440 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihg_440 v0 v1 ~v2 v3 ~v4 v5 v6 v7 = du_ihg_440 v0 v1 v3 v5 v6 v7
du_ihg_440 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihg_440 v0 v1 v2 v3 v4 v5
  = coe d_eval'7472''45'good_298 v0 v1 v2 v3 v4 v5
