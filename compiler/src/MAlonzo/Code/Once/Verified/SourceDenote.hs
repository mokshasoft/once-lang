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

module MAlonzo.Code.Once.Verified.SourceDenote where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Integer.Base
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Verified.DenotTrace
import qualified MAlonzo.Code.Once.Verified.Trace
import qualified MAlonzo.Code.Once.Verified.TraceDenote
import qualified MAlonzo.Code.Once.Verified.TraceMonad

-- Once.Verified.SourceDenote.lookupᴰ
d_lookup'7472'_12 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_lookup'7472'_12 ~v0 v1 v2 v3 = du_lookup'7472'_12 v1 v2 v3
du_lookup'7472'_12 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_lookup'7472'_12 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Syntax.C__'44'_'94'__12 v4 v5 v6
        -> case coe v1 of
             MAlonzo.Code.Data.Fin.Base.C_zero_12
               -> coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)
             MAlonzo.Code.Data.Fin.Base.C_suc_16 v8
               -> coe
                    du_lookup'7472'_12 (coe v4) (coe v8)
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Verified.SourceDenote.cata-ev-algˢ
d_cata'45'ev'45'alg'738'_36 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg'738'_36 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.Verified.TraceDenote.du_events'45'F_10 (coe v0)
            (coe (\ v5 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
            (coe v4))
         (coe
            MAlonzo.Code.Once.Verified.TraceMonad.du_projTrace_62
            (coe du_step_54 (coe v0) (coe v1) (coe v3) (coe v4)) (coe v2)))
      (coe
         MAlonzo.Code.Once.Verified.DenotTrace.d_forget_26 (coe v1)
         (coe
            MAlonzo.Code.Once.Verified.TraceMonad.du_valueT_70
            (coe du_step_54 (coe v0) (coe v1) (coe v3) (coe v4)) (coe v2)))
-- Once.Verified.SourceDenote._.z
d_z_52 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny
d_z_52 v0 ~v1 ~v2 ~v3 v4 = du_z_52 v0 v4
du_z_52 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_z_52 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Verified.SourceDenote._.step
d_step_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_54 v0 v1 ~v2 v3 v4 = du_step_54 v0 v1 v3 v4
du_step_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_54 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
      (coe v2)
      (coe
         (\ v4 ->
            coe
              v4
              (MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30
                 (coe
                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
                 (coe du_z_52 (coe v0) (coe v3)))))
-- Once.Verified.SourceDenote.ana-eventsˢ
d_ana'45'events'738'_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Verified.Trace.T_SigOpEvent_138]
d_ana'45'events'738'_62 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v5 = subInt (coe v4) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Once.Verified.TraceMonad.du_projTrace_62
                   (coe du_step_82 (coe v1) (coe v2) (coe v3)) (coe v5))
                (coe
                   MAlonzo.Code.Once.Verified.TraceDenote.du_events'45'F_10 (coe v0)
                   (coe
                      (\ v6 ->
                         d_ana'45'events'738'_62
                           (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)))
                   (coe d_layer_86 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))))
-- Once.Verified.SourceDenote._.step
d_step_82 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_82 ~v0 v1 v2 v3 ~v4 = du_step_82 v1 v2 v3
du_step_82 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_82 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
      (coe v1)
      (coe
         (\ v3 ->
            coe
              v3
              (MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30
                 (coe v0) (coe v2))))
-- Once.Verified.SourceDenote._.layer
d_layer_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> AgdaAny
d_layer_86 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 (coe v0)
      (coe
         MAlonzo.Code.Once.Verified.DenotTrace.d_forget_26
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Verified.TraceMonad.du_valueT_70
            (coe du_step_82 (coe v1) (coe v2) (coe v3)) (coe v4)))
-- Once.Verified.SourceDenote.⟦_⟧ˢ
d_'10214'_'10215''738'_98 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_50 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''738'_98 ~v0 v1 ~v2 v3 v4 v5
  = du_'10214'_'10215''738'_98 v1 v3 v4 v5
du_'10214'_'10215''738'_98 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_174 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214'_'10215''738'_98 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_182 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                  (coe du_lookup'7472'_12 (coe v0) (coe v6) (coe v3)))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_198 v7 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                         (coe
                            (\ v17 ->
                               coe
                                 du_'10214'_'10215''738'_98
                                 (coe
                                    MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0)
                                    (coe v13))
                                 (coe v15) (coe v12)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                    (coe v17)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_214 v6 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v10)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v1))
                (coe v11) (coe v3))
             (coe
                MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                (coe
                   du_'10214'_'10215''738'_98 (coe v0) (coe v8) (coe v12) (coe v3)))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_228 v6 v7 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                         (coe
                            (\ v16 ->
                               coe
                                 MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                                 (coe
                                    du_'10214'_'10215''738'_98 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v8)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                                       (coe v14))
                                    (coe v10) (coe v3))
                                 (coe
                                    MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                                    (coe
                                       du_'10214'_'10215''738'_98 (coe v0) (coe v8) (coe v11)
                                       (coe v3))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_242 v6 v7 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
               -> coe
                    MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_98 (coe v0) (coe v12) (coe v10) (coe v3))
                    (coe
                       (\ v14 ->
                          coe
                            MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                            (coe
                               du_'10214'_'10215''738'_98 (coe v0) (coe v13) (coe v11) (coe v3))
                            (coe
                               (\ v15 v16 ->
                                  coe
                                    MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                       (coe v15))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_254 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v8))
                (coe v9) (coe v3))
             (coe
                (\ v10 v11 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_266 v7 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v7) (coe v1))
                (coe v9) (coe v3))
             (coe
                (\ v10 v11 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_278 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_98 (coe v0) (coe v10) (coe v9) (coe v3))
                    (coe
                       (\ v12 v13 ->
                          coe
                            MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_290 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_98 (coe v0) (coe v11) (coe v9) (coe v3))
                    (coe
                       (\ v12 v13 ->
                          coe
                            MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_312 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v11) (coe v12))
                (coe v14) (coe v3))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v17 ->
                   coe
                     du_'10214'_'10215''738'_98
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v11))
                     (coe v1) (coe v15)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v17)))
                (\ v17 ->
                   coe
                     du_'10214'_'10215''738'_98
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v12))
                     (coe v1) (coe v16)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v17))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_318
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_328 v8
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v8) (coe v3))
             (\ v9 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_344 v6 v7 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0) (coe v9) (coe v11) (coe v3))
             (coe
                (\ v13 ->
                   coe
                     du_'10214'_'10215''738'_98
                     (coe
                        MAlonzo.Code.Once.Surface.Syntax.du__'44'__16 (coe v0) (coe v9))
                     (coe v1) (coe v12)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3) (coe v13))))
      MAlonzo.Code.Once.Surface.Syntax.C_int_350 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v6)))
      MAlonzo.Code.Once.Surface.Syntax.C_str_356 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                     (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_200
                        (coe v6))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Surface.Syntax.C_add_366 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_176
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_376 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_178
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_386 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_180
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_div_396 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_182
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_406 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_184
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_414 v7
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v7) (coe v3))
             (coe
                (\ v8 v9 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                     (coe
                        MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_186 v8)))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_424 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_188
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_434 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_190
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_444 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_192
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_454 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_194
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_464 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_196
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_474 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_198
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_486 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    du_'10214'_'10215''738'_98 (coe v0)
                    (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v10) (coe v12))
                    (coe v9) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_494 v7
        -> let v8
                 = \ v8 ->
                     coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Verified.DenotTrace.du_emit'45'D_128
                          (coe MAlonzo.Code.Once.Type.C_Unit_122)
                          (coe
                             MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_226
                             (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe
                          MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30 (coe v1)
                          (coe
                             MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                             (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_226
                                (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v9 v10 v11
                  -> coe
                       (\ v12 ->
                          coe
                            MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                            (coe
                               (\ v13 v14 ->
                                  coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                    (coe
                                       MAlonzo.Code.Once.Verified.DenotTrace.du_emit'45'D_128
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_234
                                          (coe v9) (coe v11) (coe v10) (coe v7))
                                       (coe
                                          MAlonzo.Code.Once.Verified.DenotTrace.d_forget_26 (coe v9)
                                          (coe v13)))
                                    (coe
                                       MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                                          (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_234
                                             (coe v9) (coe v11) (coe v10) (coe v7))
                                          (MAlonzo.Code.Once.Verified.DenotTrace.d_forget_26
                                             (coe v9) (coe v13)))))))
                _ -> coe v8)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_502 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Verified.DenotTrace.du_emit'45'D_128
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_226
                        (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30 (coe v1)
                     (coe
                        MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_226
                           (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_poly_512 v6
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Verified.DenotTrace.du_emit'45'D_128
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_226
                        (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v6))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30 (coe v1)
                     (coe
                        MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_166
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_226
                           (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v6))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_524 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                         (coe
                            MAlonzo.Code.Once.Verified.DenotTrace.d_eval'7472'_154 (coe v10)
                            (coe v12) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_536 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Verified.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0) (coe v7) (coe v10) (coe v3))
             (coe
                MAlonzo.Code.Once.Verified.DenotTrace.d_eval'7472'_154 (coe v7)
                (coe v1) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_548 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                             -> coe
                                  (\ v17 ->
                                     coe
                                       MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v18 v19 ->
                                             coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954
                                                     v14 v9
                                                     (d_cata'45'ev'45'alg'738'_36
                                                        (coe v14) (coe v13) (coe v19)
                                                        (coe
                                                           du_'10214'_'10215''738'_98
                                                           (coe
                                                              MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                           (coe
                                                              MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                 (coe v14) (coe v13))
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_Many_10)
                                                                 (coe v16))
                                                              (coe v13))
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                     v18))
                                               (coe
                                                  MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954
                                                        v14 v9
                                                        (d_cata'45'ev'45'alg'738'_36
                                                           (coe v14) (coe v13) (coe v19)
                                                           (coe
                                                              du_'10214'_'10215''738'_98
                                                              (coe
                                                                 MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                              (coe
                                                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                    (coe v14) (coe v13))
                                                                 (coe
                                                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                    (coe
                                                                       MAlonzo.Code.Once.Type.C_Many_10)
                                                                    (coe v16))
                                                                 (coe v13))
                                                              (coe v10)
                                                              (coe
                                                                 MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                                        v18))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_560 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v16
                             -> coe
                                  (\ v17 ->
                                     coe
                                       MAlonzo.Code.Once.Verified.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v18 v19 ->
                                             coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  d_ana'45'events'738'_62 (coe v16) (coe v11)
                                                  (coe
                                                     du_'10214'_'10215''738'_98
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                        (coe v11)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v15))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                           (coe v16) (coe v11)))
                                                     (coe v10)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe
                                                     MAlonzo.Code.Once.Verified.DenotTrace.d_forget_26
                                                     (coe v11) (coe v18))
                                                  (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114
                                                     (coe v16)
                                                     (coe
                                                        (\ v20 ->
                                                           coe
                                                             MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108
                                                             (coe v16)
                                                             (coe
                                                                MAlonzo.Code.Once.Verified.DenotTrace.d_forget_26
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                   (coe v16) (coe v11))
                                                                (coe
                                                                   MAlonzo.Code.Once.Verified.TraceMonad.du_valueT_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Verified.TraceMonad.du_valueT_70
                                                                      (coe
                                                                         du_'10214'_'10215''738'_98
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Syntax.C_'8709'_8)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                            (coe v11)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v15))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                               (coe v16) (coe v11)))
                                                                         (coe v10)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                      (0 :: Integer)
                                                                      (MAlonzo.Code.Once.Verified.DenotTrace.d_inject_30
                                                                         (coe v11) (coe v20)))
                                                                   (coe (0 :: Integer))))))
                                                     (coe
                                                        MAlonzo.Code.Once.Verified.DenotTrace.d_forget_26
                                                        (coe v11) (coe v18)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
