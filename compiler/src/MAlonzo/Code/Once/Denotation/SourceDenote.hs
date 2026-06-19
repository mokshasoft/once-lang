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

module MAlonzo.Code.Once.Denotation.SourceDenote where

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
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.SourceDenote.lookupᴰ
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
-- Once.Denotation.SourceDenote.cata-ev-algˢ
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
            MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
            (coe (\ v5 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
            (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
            (coe du_step_54 (coe v0) (coe v1) (coe v3) (coe v4)) (coe v2)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_forget_26 (coe v1)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe du_step_54 (coe v0) (coe v1) (coe v3) (coe v4)) (coe v2)))
-- Once.Denotation.SourceDenote._.z
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
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_136
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_418 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Denotation.SourceDenote._.step
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
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
      (coe v2)
      (coe
         (\ v4 ->
            coe
              v4
              (MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30
                 (coe
                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
                 (coe du_z_52 (coe v0) (coe v3)))))
-- Once.Denotation.SourceDenote.ana-eventsˢ
d_ana'45'events'738'_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_122]
d_ana'45'events'738'_62 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v5 = subInt (coe v4) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                   (coe du_step_82 (coe v1) (coe v2) (coe v3)) (coe v5))
                (coe
                   MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
                   (coe
                      (\ v6 ->
                         d_ana'45'events'738'_62
                           (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)))
                   (coe d_layer_86 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))))
-- Once.Denotation.SourceDenote._.step
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
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
      (coe v1)
      (coe
         (\ v3 ->
            coe
              v3
              (MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30
                 (coe v0) (coe v2))))
-- Once.Denotation.SourceDenote._.layer
d_layer_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> AgdaAny
d_layer_86 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_forget_26
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe du_step_82 (coe v1) (coe v2) (coe v3)) (coe v4)))
-- Once.Denotation.SourceDenote.⟦_⟧ˢ
d_'10214'_'10215''738'_98 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''738'_98 ~v0 v1 ~v2 v3 v4 v5
  = du_'10214'_'10215''738'_98 v1 v3 v4 v5
du_'10214'_'10215''738'_98 ::
  MAlonzo.Code.Once.Surface.Syntax.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_184 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214'_'10215''738'_98 v0 v1 v2 v3
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_192 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe du_lookup'7472'_12 (coe v0) (coe v6) (coe v3)))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_208 v7 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
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
      MAlonzo.Code.Once.Surface.Syntax.C_app_224 v6 v7 v8 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
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
                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                (coe
                   du_'10214'_'10215''738'_98 (coe v0) (coe v8) (coe v12) (coe v3)))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_238 v6 v7 v8 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> coe
                    (\ v15 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v16 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
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
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                    (coe
                                       du_'10214'_'10215''738'_98 (coe v0) (coe v8) (coe v11)
                                       (coe v3))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_252 v6 v7 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v12 v13
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_98 (coe v0) (coe v12) (coe v10) (coe v3))
                    (coe
                       (\ v14 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                            (coe
                               du_'10214'_'10215''738'_98 (coe v0) (coe v13) (coe v11) (coe v3))
                            (coe
                               (\ v15 v16 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                       (coe v15))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_264 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v8))
                (coe v9) (coe v3))
             (coe
                (\ v10 v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v10))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_276 v7 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v7) (coe v1))
                (coe v9) (coe v3))
             (coe
                (\ v10 v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v10))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_288 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_98 (coe v0) (coe v10) (coe v9) (coe v3))
                    (coe
                       (\ v12 v13 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_300 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_98 (coe v0) (coe v11) (coe v9) (coe v3))
                    (coe
                       (\ v12 v13 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_322 v6 v7 v8 v9 v10 v11 v12 v14 v15 v16
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
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
      MAlonzo.Code.Once.Surface.Syntax.C_unit_328
        -> coe
             (\ v6 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_338 v8
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v8) (coe v3))
             (\ v9 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_354 v6 v7 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
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
      MAlonzo.Code.Once.Surface.Syntax.C_int_360 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Data.Integer.Base.d_'8739'_'8739'_18 (coe v6)))
      MAlonzo.Code.Once.Surface.Syntax.C_str_366 v6
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                     (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_184
                        (coe v6))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Surface.Syntax.C_add_376 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_160
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_386 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_162
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_396 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_164
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_div_406 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_166
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_416 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_168
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_424 v7
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v7) (coe v3))
             (coe
                (\ v8 v9 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe
                        MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_170 v8)))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_434 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_172
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_444 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_174
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_454 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_176
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_464 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_178
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_474 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_180
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_484 v6 v7 v8 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3))
             (coe
                (\ v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_98 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3))
                     (coe
                        (\ v11 v12 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_182
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v10)
                                   (coe v11)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_496 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    du_'10214'_'10215''738'_98 (coe v0)
                    (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v10) (coe v12))
                    (coe v9) (coe v3)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_504 v7
        -> let v8
                 = \ v8 ->
                     coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.du_emit'45'D_128
                          (coe MAlonzo.Code.Once.Type.C_Unit_122)
                          (coe
                             MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_210
                             (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe
                          MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30 (coe v1)
                          (coe
                             MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                             (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_210
                                (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))) in
           coe
             (case coe v1 of
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
                                       MAlonzo.Code.Once.Denotation.DenotTrace.du_emit'45'D_128
                                       (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_218
                                          (coe v9) (coe v11) (coe v10) (coe v7))
                                       (coe
                                          MAlonzo.Code.Once.Denotation.DenotTrace.d_forget_26
                                          (coe v9) (coe v13)))
                                    (coe
                                       MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30 (coe v11)
                                       (coe
                                          MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                                          (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_218
                                             (coe v9) (coe v11) (coe v10) (coe v7))
                                          (MAlonzo.Code.Once.Denotation.DenotTrace.d_forget_26
                                             (coe v9) (coe v13)))))))
                _ -> coe v8)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_512 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.du_emit'45'D_128
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_210
                        (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30 (coe v1)
                     (coe
                        MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_210
                           (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v7))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_poly_522 v6
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.du_emit'45'D_128
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_210
                        (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v6))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30 (coe v1)
                     (coe
                        MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_150
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_210
                           (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v6))
                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_534 v9
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
               -> coe
                    (\ v13 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_154 (coe v10)
                            (coe v12) (coe v9)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_546 v6 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_98 (coe v0) (coe v7) (coe v10) (coe v3))
             (coe
                MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_154 (coe v7)
                (coe v1) (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_558 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v11 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v14
                      -> case coe v12 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                             -> coe
                                  (\ v17 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v18 v19 ->
                                             coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                                                  (coe
                                                     MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_940
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
                                                  MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                                     (coe
                                                        MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_940
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
      MAlonzo.Code.Once.Surface.Syntax.C_ana_570 v9 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v14 v15
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v16
                             -> coe
                                  (\ v17 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
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
                                                     MAlonzo.Code.Once.Denotation.DenotTrace.d_forget_26
                                                     (coe v11) (coe v18))
                                                  (coe v19))
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30
                                                  (coe v13)
                                                  (coe
                                                     MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1024
                                                     (coe v16)
                                                     (coe
                                                        (\ v20 ->
                                                           coe
                                                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_94
                                                             (coe v16)
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.DenotTrace.d_forget_26
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                   (coe v16) (coe v11))
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
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
                                                                      (MAlonzo.Code.Once.Denotation.DenotTrace.d_inject_30
                                                                         (coe v11) (coe v20)))
                                                                   (coe (0 :: Integer))))))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.DenotTrace.d_forget_26
                                                        (coe v11) (coe v18)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
