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
import qualified MAlonzo.Code.Agda.Builtin.Equality
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Nat.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.Semantics.Functor
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.DenotPrefix.const-empty-pf
d_const'45'empty'45'pf_12 ::
  MAlonzo.Code.Once.Res.T_Res_6 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_396
d_const'45'empty'45'pf_12 ~v0 = du_const'45'empty'45'pf_12
du_const'45'empty'45'pf_12 ::
  MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_396
du_const'45'empty'45'pf_12
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
      (\ v0 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
      (\ v0 ->
         coe
           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
           (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased)
-- Once.Denotation.DenotPrefix.Goodν
d_Goodν_28 a0 a1 = ()
data T_Goodν_28
  = C_constructor_54 MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_396
                     AgdaAny
-- Once.Denotation.DenotPrefix.GoodLayerRes
d_GoodLayerRes_34 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_GoodLayerRes_34 = erased
-- Once.Denotation.DenotPrefix.GoodLayer
d_GoodLayer_40 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 -> AgdaAny -> ()
d_GoodLayer_40 = erased
-- Once.Denotation.DenotPrefix.Goodν.force-pf
d_force'45'pf_50 ::
  T_Goodν_28 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_PrefixFamily_396
d_force'45'pf_50 v0
  = case coe v0 of
      C_constructor_54 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.Goodν.force-good
d_force'45'good_52 :: T_Goodν_28 -> AgdaAny
d_force'45'good_52 v0
  = case coe v0 of
      C_constructor_54 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.Good
d_Good_104 :: MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> ()
d_Good_104 = erased
-- Once.Denotation.DenotPrefix.GoodT
d_GoodT_108 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10 -> ()
d_GoodT_108 = erased
-- Once.Denotation.DenotPrefix.GoodRes
d_GoodRes_112 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> ()
d_GoodRes_112 = erased
-- Once.Denotation.DenotPrefix.GoodRes-at
d_GoodRes'45'at_186 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  AgdaAny -> AgdaAny
d_GoodRes'45'at_186 ~v0 ~v1 ~v2 ~v3 v4 = du_GoodRes'45'at_186 v4
du_GoodRes'45'at_186 :: AgdaAny -> AgdaAny
du_GoodRes'45'at_186 v0 = coe v0
-- Once.Denotation.DenotPrefix.good-bindRes
d_good'45'bindRes_204 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer ->
   [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_120]) ->
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_10) ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
d_good'45'bindRes_204 ~v0 ~v1 ~v2 v3 ~v4 v5
  = du_good'45'bindRes_204 v3 v5
du_good'45'bindRes_204 ::
  MAlonzo.Code.Once.Res.T_Res_6 ->
  (AgdaAny ->
   MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 -> AgdaAny) ->
  AgdaAny
du_good'45'bindRes_204 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Res.C_returns_12 v2 -> coe v1 v2 erased
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.injectν-Good
d_injectν'45'Good_232 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_νS_198 -> T_Goodν_28
d_injectν'45'Good_232 v0 v1
  = coe
      C_constructor_54
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
         (\ v2 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
         (\ v2 ->
            coe
              MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
              (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased))
      (coe
         d_injectν'45'layer'45'res_240 (coe v0) (coe v0)
         (coe MAlonzo.Code.Once.Semantics.Functor.d_unfoldS_204 (coe v1)))
-- Once.Denotation.DenotPrefix.injectν-layer-res
d_injectν'45'layer'45'res_240 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
d_injectν'45'layer'45'res_240 v0 v1 v2
  = case coe v2 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Res.C_returns_12 v3
        -> coe d_injectν'45'layer_248 (coe v0) (coe v1) (coe v3)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.injectν-layer
d_injectν'45'layer_248 ::
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  MAlonzo.Code.Once.Semantics.Functor.T_SFunctor_6 ->
  AgdaAny -> AgdaAny
d_injectν'45'layer_248 v0 v1 v2
  = case coe v1 of
      MAlonzo.Code.Once.Semantics.Functor.C_SK_8
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Semantics.Functor.C_SId_10
        -> coe d_injectν'45'Good_232 (coe v0) (coe v2)
      MAlonzo.Code.Once.Semantics.Functor.C__S'8853'__12 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v5
               -> coe d_injectν'45'layer_248 (coe v0) (coe v3) (coe v5)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v5
               -> coe d_injectν'45'layer_248 (coe v0) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Semantics.Functor.C__S'8855'__14 v3 v4
        -> case coe v2 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v5 v6
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_injectν'45'layer_248 (coe v0) (coe v3) (coe v5))
                    (coe d_injectν'45'layer_248 (coe v0) (coe v4) (coe v6))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.inject-Good
d_inject'45'Good_306 ::
  MAlonzo.Code.Once.Type.T_Type_108 -> AgdaAny -> AgdaAny
d_inject'45'Good_306 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_118
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C__'42'__122 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_inject'45'Good_306 (coe v2) (coe v4))
                    (coe d_inject'45'Good_306 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__124 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe d_inject'45'Good_306 (coe v2) (coe v4)
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe d_inject'45'Good_306 (coe v3) (coe v4)
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
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
                                   (\ v8 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                                   (\ v8 ->
                                      coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased))
                                (coe d_inject'45'GoodRes_312 (coe v4) (coe v1 v7)))
                    MAlonzo.Code.Once.Type.C_One_8
                      -> coe
                           (\ v7 v8 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
                                   (\ v9 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                                   (\ v9 ->
                                      coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased))
                                (coe
                                   d_inject'45'GoodRes_312 (coe v4)
                                   (coe
                                      v1
                                      (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                                         (coe v2) (coe v7)))))
                    MAlonzo.Code.Once.Type.C_Many_10
                      -> coe
                           (\ v7 v8 ->
                              coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                (coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
                                   (\ v9 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                                   (\ v9 ->
                                      coe
                                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                        (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased))
                                (coe
                                   d_inject'45'GoodRes_312 (coe v4)
                                   (coe
                                      v1
                                      (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                                         (coe v2) (coe v7)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C_μ'45'type_128 v2
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Type.C_ν'45'type_130 v2 v3
        -> coe
             d_injectν'45'Good_232
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
-- Once.Denotation.DenotPrefix.inject-GoodRes
d_inject'45'GoodRes_312 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Res.T_Res_6 -> AgdaAny
d_inject'45'GoodRes_312 v0 v1
  = case coe v1 of
      MAlonzo.Code.Once.Res.C_stopped_10
        -> coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8
      MAlonzo.Code.Once.Res.C_returns_12 v2
        -> coe d_inject'45'Good_306 (coe v0) (coe v2)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix.evalᴰ-good-Cata
d_eval'7472''45'good'45'Cata_406
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.DenotPrefix.eval\7472-good-Cata"
-- Once.Denotation.DenotPrefix.evalᴰ-good-Out
d_eval'7472''45'good'45'Out_416
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.DenotPrefix.eval\7472-good-Out"
-- Once.Denotation.DenotPrefix.evalᴰ-good-in-ν
d_eval'7472''45'good'45'in'45'ν_426
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.DenotPrefix.eval\7472-good-in-\957"
-- Once.Denotation.DenotPrefix.evalᴰ-good-Ana
d_eval'7472''45'good'45'Ana_440
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.DenotPrefix.eval\7472-good-Ana"
-- Once.Denotation.DenotPrefix.evalᴰ-good-SigOp
d_eval'7472''45'good'45'SigOp_452
  = error
      "MAlonzo Runtime Error: postulate evaluated: Once.Denotation.DenotPrefix.eval\7472-good-SigOp"
-- Once.Denotation.DenotPrefix.evalᴰ-good
d_eval'7472''45'good_464 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval'7472''45'good_464 v0 v1 v2 v3 v4
  = case coe v3 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)
                  (coe v6))
      MAlonzo.Code.Once.IR.C__'8728'__28 v6 v8 v9
        -> coe
             (\ v10 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_'62''62''61'T'45'pf_756
                     (coe
                        MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                        (coe v1) (coe v6) (coe v9) (coe v4))
                     (coe
                        MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                        (coe v6) (coe v2) (coe v8))
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                        (coe
                           du_ihf_558 (coe v0) (coe v1) (coe v6) (coe v9) (coe v4) (coe v10)))
                     (coe
                        (\ v11 v12 ->
                           MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                             (coe
                                du_ihg_562 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8) (coe v9)
                                (coe v4) (coe v10) (coe v11)))))
                  (coe
                     du_good'45'bindRes_204
                     (coe
                        MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                        (coe
                           MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                           (coe v1) (coe v6) (coe v9) (coe v4)))
                     (coe
                        (\ v11 v12 ->
                           MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                             (coe
                                du_ihg_562 (coe v0) (coe v1) (coe v2) (coe v6) (coe v8) (coe v9)
                                (coe v4) (coe v10) (coe v11))))))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v8 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    (\ v12 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_'62''62''61'T'45'pf_756
                            (coe
                               MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                               (coe v1) (coe v10) (coe v8) (coe v4))
                            (coe
                               (\ v13 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__70
                                    (coe
                                       MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                                       (coe v0) (coe v1) (coe v11) (coe v9) (coe v4))
                                    (coe
                                       (\ v14 ->
                                          coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                               (coe v14))))))
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  du_ihf_596 (coe v0) (coe v1) (coe v10) (coe v8) (coe v4)
                                  (coe v12)))
                            (coe
                               (\ v13 v14 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_'62''62''61'T'45'pf_756
                                    (coe
                                       MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                                       (coe v0) (coe v1) (coe v11) (coe v9) (coe v4))
                                    (coe
                                       (\ v15 ->
                                          coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_34
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                               (coe v15))))
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                       (coe
                                          du_ihg_598 (coe v0) (coe v1) (coe v11) (coe v9) (coe v4)
                                          (coe v12)))
                                    (coe
                                       (\ v15 v16 ->
                                          coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)))))
                         (coe
                            du_good'45'bindRes_204
                            (coe
                               MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                               (coe
                                  MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12 (coe v0)
                                  (coe v1) (coe v10) (coe v8) (coe v4)))
                            (coe
                               (\ v13 v14 ->
                                  coe
                                    du_good'45'bindRes_204
                                    (coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.d_resT_20
                                       (coe
                                          MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                                          (coe v0) (coe v1) (coe v11) (coe v9) (coe v4)))
                                    (coe
                                       (\ v15 v16 ->
                                          coe
                                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  du_ihf_596 (coe v0) (coe v1) (coe v10) (coe v8)
                                                  (coe v4) (coe v12)))
                                            (coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                               (coe
                                                  du_ihg_598 (coe v0) (coe v1) (coe v11) (coe v9)
                                                  (coe v4) (coe v12)))))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v7)))
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)
                  (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)
                  (coe v7))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)
                  (coe v7))
      MAlonzo.Code.Once.IR.C_case_68 v8 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v10 v11
               -> case coe v4 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                      -> coe (\ v13 -> coe d_eval'7472''45'good_464 v0 v10 v2 v8 v12 v13)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                      -> coe (\ v13 -> coe d_eval'7472''45'good_464 v0 v11 v2 v9 v12 v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.IR.C_curry_84 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v9 v10
               -> coe
                    (\ v11 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT'45'pf_420)
                         (coe
                            (\ v12 v13 ->
                               coe
                                 d_eval'7472''45'good_464 v0
                                 (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v9)) v10 v8
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v12))
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                    (coe v13)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v7
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                  (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v7)))
      MAlonzo.Code.Once.IR.C_In_94 v6
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    (\ v8 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
                            (\ v9 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                            (\ v9 ->
                               coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased))
                         (coe
                            d_inject'45'Good_306
                            (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622 (coe v2))
                            (coe
                               MAlonzo.Code.Once.Denotation.DenotTrace.d_in'45'val_16 (coe v7)
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                                  (coe
                                     MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7)
                                        (coe v2)))
                                  (coe v4)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v7
               -> coe
                    (\ v8 ->
                       coe
                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                         (coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
                            (\ v9 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                            (\ v9 ->
                               coe
                                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                 (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased))
                         (coe
                            d_inject'45'Good_306
                            (coe
                               MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622
                               (coe
                                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v7) (coe v1)))
                            (coe
                               MAlonzo.Code.Once.Denotation.DenotTrace.d_out'45'μ'45'val_20
                               (coe v7) (coe v6)
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_510
                                  (coe
                                     MAlonzo.Code.Once.Type.C_μ'45'type_128
                                     (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_624 (coe v7)))
                                  (coe v4)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v6 v9
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> case coe v11 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v12
                      -> coe
                           (\ v13 ->
                              coe d_eval'7472''45'good'45'Cata_406 v0 v12 v6 v10 v2 v9 v4 v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v6
        -> case coe v1 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe (\ v8 -> coe d_eval'7472''45'good'45'Out_416 v0 v7 v6 v4 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v6
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v7
               -> coe
                    (\ v8 -> coe d_eval'7472''45'good'45'in'45'ν_426 v0 v7 v6 v4 v8)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_120 v6 v8
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
               -> coe
                    (\ v10 ->
                       coe d_eval'7472''45'good'45'Ana_440 v0 v9 v6 v1 v8 v4 v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_124 v6 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.C_prefixFamily_414
                     (\ v9 -> coe MAlonzo.Code.Data.Nat.Base.C_z'8804'n_26)
                     (\ v9 ->
                        coe
                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) erased))
                  (coe
                     d_inject'45'Good_306
                     (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_622 (coe v2))
                     (coe
                        MAlonzo.Code.Once.Denotation.DenotTrace.du_const'45'val_26 (coe v0)
                        (coe v6) (coe v7))))
      MAlonzo.Code.Once.IR.C_SigOp_130 v5 v6 v7
        -> coe
             (\ v8 -> coe d_eval'7472''45'good'45'SigOp_452 v0 v5 v6 v7 v4 v8)
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotPrefix._.ihf
d_ihf_558 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihf_558 v0 v1 ~v2 v3 ~v4 v5 v6 v7 = du_ihf_558 v0 v1 v3 v5 v6 v7
du_ihf_558 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihf_558 v0 v1 v2 v3 v4 v5
  = coe d_eval'7472''45'good_464 v0 v1 v2 v3 v4 v5
-- Once.Denotation.DenotPrefix._.ihg
d_ihg_562 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny ->
  AgdaAny ->
  MAlonzo.Code.Agda.Builtin.Equality.T__'8801'__12 ->
  MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihg_562 v0 v1 v2 v3 v4 v5 v6 v7 v8 ~v9
  = du_ihg_562 v0 v1 v2 v3 v4 v5 v6 v7 v8
du_ihg_562 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihg_562 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      d_eval'7472''45'good_464 v0 v3 v2 v4 v8
      (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
         (coe
            du_ihf_558 (coe v0) (coe v1) (coe v3) (coe v5) (coe v6) (coe v7)))
-- Once.Denotation.DenotPrefix._.ihf
d_ihf_596 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihf_596 v0 v1 v2 ~v3 v4 ~v5 v6 v7 = du_ihf_596 v0 v1 v2 v4 v6 v7
du_ihf_596 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihf_596 v0 v1 v2 v3 v4 v5
  = coe d_eval'7472''45'good_464 v0 v1 v2 v3 v4 v5
-- Once.Denotation.DenotPrefix._.ihg
d_ihg_598 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_ihg_598 v0 v1 ~v2 v3 ~v4 v5 v6 v7 = du_ihg_598 v0 v1 v3 v5 v6 v7
du_ihg_598 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_ihg_598 v0 v1 v2 v3 v4 v5
  = coe d_eval'7472''45'good_464 v0 v1 v2 v3 v4 v5
