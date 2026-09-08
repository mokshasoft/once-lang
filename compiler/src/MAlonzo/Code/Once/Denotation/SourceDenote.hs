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
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Surface.Context
import qualified MAlonzo.Code.Once.Surface.Syntax
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type
import qualified MAlonzo.Code.Once.Word

-- Once.Denotation.SourceDenote.lookupᴰ
d_lookup'7472'_12 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_lookup'7472'_12 ~v0 v1 v2 v3 = du_lookup'7472'_12 v1 v2 v3
du_lookup'7472'_12 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_lookup'7472'_12 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Surface.Context.C__'44'_'94'__12 v4 v5 v6
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
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg'738'_36 v0 ~v1 v2 v3 v4
  = du_cata'45'ev'45'alg'738'_36 v0 v2 v3 v4
du_cata'45'ev'45'alg'738'_36 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_cata'45'ev'45'alg'738'_36 v0 v1 v2 v3
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
            (coe du_step_54 (coe v0) (coe v2) (coe v3)) (coe v1)))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
         (coe du_step_54 (coe v0) (coe v2) (coe v3)) (coe v1))
-- Once.Denotation.SourceDenote._.z
d_z_52 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> AgdaAny
d_z_52 v0 ~v1 ~v2 ~v3 v4 = du_z_52 v0 v4
du_z_52 ::
  MAlonzo.Code.Once.Type.T_Functor_106 -> AgdaAny -> AgdaAny
du_z_52 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_260
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_434 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Denotation.SourceDenote._.step
d_step_54 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_54 v0 ~v1 ~v2 v3 v4 = du_step_54 v0 v3 v4
du_step_54 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
      (coe v1) (coe (\ v3 -> coe v3 (coe du_z_52 (coe v0) (coe v2))))
-- Once.Denotation.SourceDenote.ana-eventsˢ
d_ana'45'events'738'_62 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
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
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_82 ~v0 v1 v2 v3 ~v4 = du_step_82 v1 v2 v3
du_step_82 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
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
              (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92
                 (coe v0) (coe v2))))
-- Once.Denotation.SourceDenote._.layer
d_layer_86 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> AgdaAny
d_layer_86 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_110 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe du_step_82 (coe v1) (coe v2) (coe v3)) (coe v4)))
-- Once.Denotation.SourceDenote.liftD
d_liftD_96 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_liftD_96 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_414 (coe v0)
         (coe v1) (coe v2) (coe v3))
-- Once.Denotation.SourceDenote.⟦_⟧ˢ
d_'10214'_'10215''738'_114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''738'_114 v0 v1 ~v2 v3 v4 v5 v6
  = du_'10214'_'10215''738'_114 v0 v1 v3 v4 v5 v6
du_'10214'_'10215''738'_114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214'_'10215''738'_114 v0 v1 v2 v3 v4 v5
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v8
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Denotation.Phase.du_lookup'7472'Used_12 (coe v1)
                     (coe v8) (coe v5)))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v9 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v18 v19
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         (\ v20 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                              (coe
                                                 (\ v21 ->
                                                    coe
                                                      du_'10214'_'10215''738'_114
                                                      (coe addInt (coe (1 :: Integer)) (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                         (coe v1) (coe v15))
                                                      (coe v17) (coe v14) (coe v4) (coe v5))))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe (\ v20 -> MAlonzo.RTE.mazUnreachableError)
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe (\ v20 -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Type.C_One_8
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         (\ v20 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                              (coe
                                                 (\ v21 ->
                                                    coe
                                                      du_'10214'_'10215''738'_114
                                                      (coe addInt (coe (1 :: Integer)) (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                         (coe v1) (coe v15))
                                                      (coe v17) (coe v14) (coe v4) (coe v5))))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         (\ v20 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                              (coe
                                                 (\ v21 ->
                                                    coe
                                                      du_'10214'_'10215''738'_114
                                                      (coe addInt (coe (1 :: Integer)) (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                         (coe v1) (coe v15))
                                                      (coe v17) (coe v14) (coe v4)
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                         (coe v9) (coe v5) (coe v21)))))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe (\ v20 -> MAlonzo.RTE.mazUnreachableError)
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> case coe v9 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         (\ v20 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                              (coe
                                                 (\ v21 ->
                                                    coe
                                                      du_'10214'_'10215''738'_114
                                                      (coe addInt (coe (1 :: Integer)) (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                         (coe v1) (coe v15))
                                                      (coe v17) (coe v14) (coe v4) (coe v5))))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         (\ v20 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                              (coe
                                                 (\ v21 ->
                                                    coe
                                                      du_'10214'_'10215''738'_114
                                                      (coe addInt (coe (1 :: Integer)) (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                         (coe v1) (coe v15))
                                                      (coe v17) (coe v14) (coe v4)
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                         (coe v9) (coe v5) (coe v21)))))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         (\ v20 ->
                                            coe
                                              MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                              (coe
                                                 (\ v21 ->
                                                    coe
                                                      du_'10214'_'10215''738'_114
                                                      (coe addInt (coe (1 :: Integer)) (coe v0))
                                                      (coe
                                                         MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                         (coe v1) (coe v15))
                                                      (coe v17) (coe v14) (coe v4)
                                                      (coe
                                                         MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                         (coe v9) (coe v5) (coe v21)))))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v8 v9 v10 v12 v13 v14
        -> case coe v12 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v12)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v13) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                (coe v9)))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                (coe v9)))
                          (coe v5)))
                    (coe
                       (\ v15 -> coe v15 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             MAlonzo.Code.Once.Type.C_One_8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v12)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v13) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                (coe v9)))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                (coe v9)))
                          (coe v5)))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                       (coe
                          du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v10) (coe v14)
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                   (coe v9)))
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v12) (coe v9)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                   (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v12) (coe v9))))
                             (coe v5))))
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v12)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v13) (coe v4)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                (coe v9)))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                (coe v9)))
                          (coe v5)))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                       (coe
                          du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v10) (coe v14)
                          (coe v4)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                   (coe v9)))
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v12)
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v12) (coe v9)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                   (coe v9))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                   (coe v8)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v12) (coe v9))))
                             (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v8 v9 v10 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v18 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                 (coe
                                    du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v10)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                                       (coe v16))
                                    (coe v12) (coe v4)
                                    (coe
                                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                       (coe v1)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                          (coe v8) (coe v9))
                                       (coe v8)
                                       (coe
                                          MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                          (coe v8) (coe v9))
                                       (coe v5)))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                    (coe
                                       du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v10)
                                       (coe v13) (coe v4)
                                       (coe
                                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                          (coe v1)
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                             (coe v8) (coe v9))
                                          (coe v9)
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                             (coe v8) (coe v9))
                                          (coe v5)))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v8 v9 v12 v13
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__122 v14 v15
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v14) (coe v12)
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                             (coe v9))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v8) (coe v9))
                          (coe v5)))
                    (coe
                       (\ v16 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                            (coe
                               du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v15) (coe v13)
                               (coe v4)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                     (coe v9))
                                  (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                     (coe v8) (coe v9))
                                  (coe v5)))
                            (coe
                               (\ v17 v18 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v16)
                                       (coe v17))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v2) (coe v10))
                (coe v11) (coe v4) (coe v5))
             (coe
                (\ v12 v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v12))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v9 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v9) (coe v2))
                (coe v11) (coe v4) (coe v5))
             (coe
                (\ v12 v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v12))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v12) (coe v11)
                       (coe v4) (coe v5))
                    (coe
                       (\ v14 v15 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v14))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__124 v12 v13
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v13) (coe v11)
                       (coe v4) (coe v5))
                    (coe
                       (\ v14 v15 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v14))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v8 v9 v10 v11 v12 v13 v14 v16 v17 v18
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__124 (coe v13) (coe v14))
                (coe v16) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                         (coe v10)))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                         (coe v10)))
                   (coe v5)))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v19 ->
                   coe
                     du_'10214'_'10215''738'_114
                     (coe addInt (coe (1 :: Integer)) (coe v0))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v13))
                     (coe v2) (coe v17) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v11)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                              (coe v10))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
                              (coe v9) (coe v10))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                                    (coe v10)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                                 (coe v10))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                                    (coe v10)))
                              (coe v5)))
                        (coe v19)))
                (\ v19 ->
                   coe
                     du_'10214'_'10215''738'_114
                     (coe addInt (coe (1 :: Integer)) (coe v0))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v14))
                     (coe v2) (coe v18) (coe v4)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v12)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
                              (coe v9) (coe v10))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                                    (coe v10)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                                 (coe v10))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v9)
                                    (coe v10)))
                              (coe v5)))
                        (coe v19))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_120) (coe v10) (coe v4)
                (coe v5))
             (\ v11 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v8 v9 v10 v11 v13 v14
        -> case coe v10 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe
                    du_'10214'_'10215''738'_114
                    (coe addInt (coe (1 :: Integer)) (coe v0))
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v11))
                    (coe v2) (coe v14) (coe v4)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                             (coe v8)))
                       (coe v9)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                             (coe v8)))
                       (coe v5))
             MAlonzo.Code.Once.Type.C_One_8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v11) (coe v13)
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                (coe v8)))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                (coe v8))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                   (coe v8)))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                (coe v8))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                   (coe v8))))
                          (coe v5)))
                    (coe
                       (\ v15 ->
                          coe
                            du_'10214'_'10215''738'_114
                            (coe addInt (coe (1 :: Integer)) (coe v0))
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v11))
                            (coe v2) (coe v14) (coe v4)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v10)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v10) (coe v8)))
                                  (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                     (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v10) (coe v8)))
                                  (coe v5))
                               (coe v15))))
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v11) (coe v13)
                       (coe v4)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                (coe v8)))
                          (coe v8)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                             (coe v8)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                (coe v8))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                   (coe v8)))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                (coe v8))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v10)
                                   (coe v8))))
                          (coe v5)))
                    (coe
                       (\ v15 ->
                          coe
                            du_'10214'_'10215''738'_114
                            (coe addInt (coe (1 :: Integer)) (coe v0))
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v11))
                            (coe v2) (coe v14) (coe v4)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v10)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v10) (coe v8)))
                                  (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                     (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v10) (coe v8)))
                                  (coe v5))
                               (coe v15))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v8
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Word.d_fromℤ_20
                     (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v4))
                     (coe v8)))
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v8
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.SigOp.Info.du_semM_188
                     (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_408
                        (coe v8))
                     v4 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v8
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Float.Decimal.d_round_174
                     (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v4))
                     (coe v8)))
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_370 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_372 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_374 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_386 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_388 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_390 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_134) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_392 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9) (coe v4) (coe v5))
             (coe
                (\ v10 v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_394 v4 v10)))
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_376 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_378 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v9) (coe v4) (coe v5))
             (coe
                (\ v10 v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_380 v4 v10)))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_396 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_398 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_400 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_402 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_404 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v8 v9 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v10) (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                      (coe v9))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v8) (coe v9))
                   (coe v5)))
             (coe
                (\ v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_132) (coe v11) (coe v4)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                              (coe v9))
                           (coe v9)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v8) (coe v9))
                           (coe v5)))
                     (coe
                        (\ v13 v14 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_406 v4
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v12)
                                   (coe v13)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_376 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> coe
                    du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                    (coe MAlonzo.Code.Once.Type.d__'8658'__146 (coe v12) (coe v14))
                    (coe v11) (coe v4) (coe v5)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v9 v10
        -> let v11
                 = \ v11 ->
                     coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_234
                          (coe MAlonzo.Code.Once.Type.C_Unit_118)
                          (coe
                             MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_422
                             (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v2) (coe v9)
                             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                             (coe v10))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92 (coe v2)
                          (coe
                             MAlonzo.Code.Once.SigOp.Info.du_semM_188
                             (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_422
                                (coe MAlonzo.Code.Once.Type.C_Unit_118) (coe v2) (coe v9)
                                (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                                (coe v10))
                             v4 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))) in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
                  -> case coe v13 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                         -> case coe v15 of
                              MAlonzo.Code.Once.Type.C_Zero_6
                                -> case coe v10 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v20 v21
                                       -> coe
                                            (\ v22 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                 (coe
                                                    (\ v23 v24 ->
                                                       coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_234
                                                            (coe MAlonzo.Code.Once.Type.C_Unit_118)
                                                            (coe
                                                               MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_422
                                                               (coe
                                                                  MAlonzo.Code.Once.Type.C_Unit_118)
                                                               (coe v14) (coe v9)
                                                               (coe
                                                                  MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                                                               (coe v21))
                                                            (coe
                                                               MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                         (coe
                                                            MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92
                                                            (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                               (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_422
                                                                  (coe
                                                                     MAlonzo.Code.Once.Type.C_Unit_118)
                                                                  (coe v14) (coe v9)
                                                                  (coe
                                                                     MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                                                                  (coe v21))
                                                               v4
                                                               (coe
                                                                  MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))))
                                     _ -> coe v11
                              MAlonzo.Code.Once.Type.C_One_8
                                -> case coe v10 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v20 v21
                                       -> coe
                                            (\ v22 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                 (coe
                                                    (\ v23 v24 ->
                                                       coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_234
                                                            (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_464
                                                               (coe v12) (coe v14) (coe v13)
                                                               (coe v9) (coe v20) (coe v21))
                                                            (coe
                                                               MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
                                                               (coe v12) (coe v23)))
                                                         (coe
                                                            MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92
                                                            (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                               (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_464
                                                                  (coe v12) (coe v14) (coe v13)
                                                                  (coe v9) (coe v20) (coe v21))
                                                               v4
                                                               (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
                                                                  (coe v12) (coe v23)))))))
                                     _ -> coe v11
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> case coe v10 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v20 v21
                                       -> coe
                                            (\ v22 ->
                                               coe
                                                 MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                 (coe
                                                    (\ v23 v24 ->
                                                       coe
                                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                         (coe
                                                            MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_234
                                                            (coe v12)
                                                            (coe
                                                               MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_464
                                                               (coe v12) (coe v14) (coe v13)
                                                               (coe v9) (coe v20) (coe v21))
                                                            (coe
                                                               MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
                                                               (coe v12) (coe v23)))
                                                         (coe
                                                            MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92
                                                            (coe v14)
                                                            (coe
                                                               MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                               (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_464
                                                                  (coe v12) (coe v14) (coe v13)
                                                                  (coe v9) (coe v20) (coe v21))
                                                               v4
                                                               (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
                                                                  (coe v12) (coe v23)))))))
                                     _ -> coe v11
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v11)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v9
        -> coe
             (\ v10 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_234
                     (coe MAlonzo.Code.Once.Type.C_Unit_118)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_432
                        (coe v2) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v9)))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92 (coe v2)
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_432
                           (coe v2) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v9)))
                        v4 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v8
        -> coe
             (\ v10 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_234
                     (coe MAlonzo.Code.Once.Type.C_Unit_118)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_432
                        (coe v2) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v8)))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92 (coe v2)
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_432
                           (coe v2) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v8)))
                        v4 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_414 v11
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v12 v13 v14
               -> coe d_liftD_96 (coe v4) (coe v12) (coe v14) (coe v11)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_426 v8 v9 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v1) (coe v9) (coe v12)
                (coe v4)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                      (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                   (coe v8)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                      (coe v8)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8)))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                         (coe v8))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v8))))
                   (coe v5)))
             (coe
                (\ v13 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                     (coe v4) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v9))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_52 (coe v2)) (coe v11)
                     (coe v13)))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_444 v8 v9 v11 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
               -> case coe v17 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                           (coe
                              du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v11)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                 (coe v18))
                              (coe v14) (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                    (coe v9))
                                 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                    (coe v8) (coe v9))
                                 (coe v5)))
                           (coe
                              (\ v21 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                   (coe
                                      du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v16)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                         (coe v11))
                                      (coe v15) (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v8) (coe v9))
                                         (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                            (coe v8) (coe v9))
                                         (coe v5)))
                                   (coe
                                      (\ v22 v23 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                           (coe
                                              (\ v24 ->
                                                 coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                                   (coe v22 v24) (coe v21)))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_462 v8 v9 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
               -> case coe v16 of
                    MAlonzo.Code.Once.Type.C__'43'__124 v19 v20
                      -> case coe v17 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v21 v22
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                  (coe
                                     du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v19)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                        (coe v18))
                                     (coe v14) (coe v4)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe v8) (coe v9))
                                        (coe v8)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                           (coe v8) (coe v9))
                                        (coe v5)))
                                  (coe
                                     (\ v23 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                          (coe
                                             du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                (coe v20)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v22))
                                                (coe v18))
                                             (coe v15) (coe v4)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe v8) (coe v9))
                                                (coe v9)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                                   (coe v8) (coe v9))
                                                (coe v5)))
                                          (coe
                                             (\ v24 v25 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v23 v24)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_478 v8 v9 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v15 v16 v17
               -> case coe v17 of
                    MAlonzo.Code.Once.Type.C__'42'__122 v18 v19
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                           (coe
                              du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                 (coe v18))
                              (coe v13) (coe v4)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v8)
                                    (coe v9))
                                 (coe v8)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                    (coe v8) (coe v9))
                                 (coe v5)))
                           (coe
                              (\ v20 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                   (coe
                                      du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 (coe v15)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10)
                                            (coe MAlonzo.Code.Once.Type.C_pure_34))
                                         (coe v19))
                                      (coe v14) (coe v4)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v8) (coe v9))
                                         (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                            (coe v8) (coe v9))
                                         (coe v5)))
                                   (coe
                                      (\ v21 v22 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                           (coe
                                              (\ v23 ->
                                                 coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                                   (coe v20 v23)
                                                   (coe
                                                      (\ v24 ->
                                                         coe
                                                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                                           (coe v21 v23)
                                                           (coe
                                                              (\ v25 v26 ->
                                                                 coe
                                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                                   (coe
                                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                      (coe v24) (coe v25))))))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_492 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v16 v17 v18
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                           (coe
                              du_'10214'_'10215''738'_114 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                 (coe MAlonzo.Code.Once.Type.C__'42'__122 (coe v13) (coe v16))
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10)
                                    (coe MAlonzo.Code.Once.Type.C_pure_34))
                                 (coe v18))
                              (coe v12) (coe v4) (coe v5))
                           (coe
                              (\ v19 v20 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                   (coe
                                      (\ v21 v22 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                           (coe
                                              (\ v23 ->
                                                 coe
                                                   v19
                                                   (coe
                                                      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                      (coe v21) (coe v23))))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_504 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_128 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v17 v18
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                  (coe
                                     du_'10214'_'10215''738'_114 (coe (0 :: Integer))
                                     (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v16)
                                           (coe v15))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v18))
                                        (coe v15))
                                     (coe v12) (coe v4) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                  (coe
                                     (\ v19 v20 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                          (coe
                                             (\ v21 v22 ->
                                                coe
                                                  MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_956
                                                  v16 v11
                                                  (coe
                                                     du_cata'45'ev'45'alg'738'_36 (coe v16)
                                                     (coe v22)
                                                     (\ v23 ->
                                                        coe
                                                          MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                                          (coe v19)))
                                                  v21))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_516 v11 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126 v13 v14 v15
               -> case coe v14 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                      -> case coe v15 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_130 v18
                             -> coe
                                  (\ v19 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v20 v21 ->
                                             coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  d_ana'45'events'738'_62 (coe v18) (coe v13)
                                                  (coe
                                                     du_'10214'_'10215''738'_114
                                                     (coe (0 :: Integer))
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                        (coe v13)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v17))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                           (coe v18) (coe v13)))
                                                     (coe v12) (coe v4)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
                                                     (coe v13) (coe v20))
                                                  (coe v21))
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92
                                                  (coe v15)
                                                  (coe
                                                     MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1040
                                                     (coe v18)
                                                     (coe
                                                        (\ v22 ->
                                                           coe
                                                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_110
                                                             (coe v18)
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                   (coe v18) (coe v13))
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                                      (coe
                                                                         du_'10214'_'10215''738'_114
                                                                         (coe (0 :: Integer))
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__126
                                                                            (coe v13)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v17))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                                               (coe v18) (coe v13)))
                                                                         (coe v12) (coe v4)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                      (0 :: Integer)
                                                                      (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_92
                                                                         (coe v13) (coe v22)))
                                                                   (coe (0 :: Integer))))))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_88
                                                        (coe v13) (coe v20)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
