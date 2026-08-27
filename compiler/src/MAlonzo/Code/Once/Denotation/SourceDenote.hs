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
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg'738'_36 v0 ~v1 v2 v3 v4
  = du_cata'45'ev'45'alg'738'_36 v0 v2 v3 v4
du_cata'45'ev'45'alg'738'_36 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
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
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Denotation.SourceDenote._.step
d_step_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_54 v0 ~v1 ~v2 v3 v4 = du_step_54 v0 v3 v4
du_step_54 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_54 v0 v1 v2
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
      (coe v1) (coe (\ v3 -> coe v3 (coe du_z_52 (coe v0) (coe v2))))
-- Once.Denotation.SourceDenote.ana-eventsˢ
d_ana'45'events'738'_62 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
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
              (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                 (coe v0) (coe v2))))
-- Once.Denotation.SourceDenote._.layer
d_layer_86 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  (Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14) ->
  AgdaAny -> Integer -> AgdaAny
d_layer_86 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96 (coe v0)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe du_step_82 (coe v1) (coe v2) (coe v3)) (coe v4)))
-- Once.Denotation.SourceDenote.liftD
d_liftD_96 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_liftD_96 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_404 (coe v0)
         (coe v1) (coe v2) (coe v3))
-- Once.Denotation.SourceDenote.⟦_⟧ˢ
d_'10214'_'10215''738'_114 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_'10214'_'10215''738'_114 ~v0 v1 ~v2 v3 v4 v5 v6
  = du_'10214'_'10215''738'_114 v1 v3 v4 v5 v6
du_'10214'_'10215''738'_114 ::
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_'10214'_'10215''738'_114 v0 v1 v2 v3 v4
  = case coe v2 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe du_lookup'7472'_12 (coe v0) (coe v7) (coe v4)))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_32 v8 v13
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v14 v15 v16
               -> coe
                    (\ v17 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v18 ->
                               coe
                                 du_'10214'_'10215''738'_114
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0)
                                    (coe v14))
                                 (coe v16) (coe v13) (coe v3)
                                 (coe
                                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                    (coe v18)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_48 v7 v8 v9 v11 v12 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe
                   MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                   (coe
                      MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v11)
                      (coe MAlonzo.Code.Once.Type.C_pure_34))
                   (coe v1))
                (coe v12) (coe v3) (coe v4))
             (coe
                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                (coe
                   du_'10214'_'10215''738'_114 (coe v0) (coe v9) (coe v13) (coe v3)
                   (coe v4)))
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_62 v7 v8 v9 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v13 v14 v15
               -> coe
                    (\ v16 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                         (coe
                            (\ v17 ->
                               coe
                                 MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                 (coe
                                    du_'10214'_'10215''738'_114 (coe v0)
                                    (coe
                                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 (coe v9)
                                       (coe
                                          MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                          (coe MAlonzo.Code.Once.Type.C_Many_10)
                                          (coe MAlonzo.Code.Once.Type.C_eff_36))
                                       (coe v15))
                                    (coe v11) (coe v3) (coe v4))
                                 (coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                                    (coe
                                       du_'10214'_'10215''738'_114 (coe v0) (coe v9) (coe v12)
                                       (coe v3) (coe v4))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_76 v7 v8 v11 v12
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'42'__126 v13 v14
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v13) (coe v11) (coe v3)
                       (coe v4))
                    (coe
                       (\ v15 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                            (coe
                               du_'10214'_'10215''738'_114 (coe v0) (coe v14) (coe v12) (coe v3)
                               (coe v4))
                            (coe
                               (\ v16 v17 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v15)
                                       (coe v16))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_88 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v1) (coe v9))
                (coe v10) (coe v3) (coe v4))
             (coe
                (\ v11 v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v11))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_100 v8 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v8) (coe v1))
                (coe v10) (coe v3) (coe v4))
             (coe
                (\ v11 v12 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v11))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_112 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v11) (coe v10) (coe v3)
                       (coe v4))
                    (coe
                       (\ v13 v14 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_124 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'43'__128 v11 v12
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                    (coe
                       du_'10214'_'10215''738'_114 (coe v0) (coe v12) (coe v10) (coe v3)
                       (coe v4))
                    (coe
                       (\ v13 v14 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v13))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_146 v7 v8 v9 v10 v11 v12 v13 v15 v16 v17
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C__'43'__128 (coe v12) (coe v13))
                (coe v15) (coe v3) (coe v4))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v18 ->
                   coe
                     du_'10214'_'10215''738'_114
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v12))
                     (coe v1) (coe v16) (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v18)))
                (\ v18 ->
                   coe
                     du_'10214'_'10215''738'_114
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v13))
                     (coe v1) (coe v17) (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v18))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_152
        -> coe
             (\ v7 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_162 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Void_124) (coe v9) (coe v3) (coe v4))
             (\ v10 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_178 v7 v8 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v10) (coe v12) (coe v3)
                (coe v4))
             (coe
                (\ v14 ->
                   coe
                     du_'10214'_'10215''738'_114
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v0) (coe v10))
                     (coe v1) (coe v13) (coe v3)
                     (coe
                        MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4) (coe v14))))
      MAlonzo.Code.Once.Surface.Syntax.C_int_184 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Word.d_fromℤ_20
                     (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v3))
                     (coe v7)))
      MAlonzo.Code.Once.Surface.Syntax.C_str_190 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.SigOp.Info.du_semM_188
                     (MAlonzo.Code.Once.Arith.SigOp.Builders.d_str'45'lit'45'info_398
                        (coe v7))
                     v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v7
        -> coe
             (\ v8 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     MAlonzo.Code.Once.Float.Decimal.d_round_174
                     (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v3))
                     (coe v7)))
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_362 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_364 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_366 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v9) (coe v3)
                (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v10) (coe v3)
                        (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_378 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v9) (coe v3)
                (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v10) (coe v3)
                        (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_380 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v9) (coe v3)
                (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Float_138) (coe v10) (coe v3)
                        (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_382 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_266 v8
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3) (coe v4))
             (coe
                (\ v9 v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_384 v3 v9)))
      MAlonzo.Code.Once.Surface.Syntax.C_div_276 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_368 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_286 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_370 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_294 v8
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v8) (coe v3) (coe v4))
             (coe
                (\ v9 v10 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_372 v3 v9)))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_304 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_386 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_314 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_388 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_324 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_390 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_334 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_392 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_344 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_394 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_354 v7 v8 v9 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0)
                (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v9) (coe v3) (coe v4))
             (coe
                (\ v11 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                     (coe
                        du_'10214'_'10215''738'_114 (coe v0)
                        (coe MAlonzo.Code.Once.Type.C_Int_136) (coe v10) (coe v3) (coe v4))
                     (coe
                        (\ v12 v13 ->
                           coe
                             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                             (coe
                                MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_396 v3
                                (coe
                                   MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v11)
                                   (coe v12)))))))
      MAlonzo.Code.Once.Surface.Syntax.C_arr''_366 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> coe
                    du_'10214'_'10215''738'_114 (coe v0)
                    (coe MAlonzo.Code.Once.Type.d__'8658'__150 (coe v11) (coe v13))
                    (coe v10) (coe v3) (coe v4)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_374 v8 v9
        -> let v10
                 = \ v10 ->
                     coe
                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                          (coe MAlonzo.Code.Once.Type.C_Unit_122)
                          (coe
                             MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_412
                             (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v8)
                             (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                             (coe v9))
                          (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v1)
                          (coe
                             MAlonzo.Code.Once.SigOp.Info.du_semM_188
                             (MAlonzo.Code.Once.Arith.SigOp.Builders.d_value'45'info_412
                                (coe MAlonzo.Code.Once.Type.C_Unit_122) (coe v1) (coe v8)
                                (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_202)
                                (coe v9))
                             v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))) in
           coe
             (case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
                  -> case coe v9 of
                       MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_238 v17 v18
                         -> coe
                              (\ v19 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                   (coe
                                      (\ v20 v21 ->
                                         coe
                                           MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                           (coe
                                              MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                                              (coe v11)
                                              (coe
                                                 MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_454
                                                 (coe v11) (coe v13) (coe v12) (coe v8) (coe v17)
                                                 (coe v18))
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                 (coe v11) (coe v20)))
                                           (coe
                                              MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                              (coe v13)
                                              (coe
                                                 MAlonzo.Code.Once.SigOp.Info.du_semM_188
                                                 (MAlonzo.Code.Once.Arith.SigOp.Builders.d_arrow'45'info_454
                                                    (coe v11) (coe v13) (coe v12) (coe v8) (coe v17)
                                                    (coe v18))
                                                 v3
                                                 (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                    (coe v11) (coe v20)))))))
                       _ -> coe v10
                _ -> coe v10)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_382 v8
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_422
                        (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v8)))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v1)
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_422
                           (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v8)))
                        v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_poly_392 v7
        -> coe
             (\ v9 ->
                coe
                  MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158
                     (coe MAlonzo.Code.Once.Type.C_Unit_122)
                     (coe
                        MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_422
                        (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v7)))
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                  (coe
                     MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v1)
                     (coe
                        MAlonzo.Code.Once.SigOp.Info.du_semM_188
                        (MAlonzo.Code.Once.Arith.SigOp.Builders.d_internal'45'info_422
                           (coe v1) (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v7)))
                        v3 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))))
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_404 v10
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
               -> coe d_liftD_96 (coe v3) (coe v11) (coe v13) (coe v10)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_416 v7 v8 v10 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
             (coe
                du_'10214'_'10215''738'_114 (coe v0) (coe v8) (coe v11) (coe v3)
                (coe v4))
             (coe
                (\ v12 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_12
                     (coe v3) (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v8))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1)) (coe v10)
                     (coe v12)))
      MAlonzo.Code.Once.Surface.Syntax.C_cata_428 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> case coe v12 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_132 v15
                      -> case coe v13 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                             -> coe
                                  (\ v18 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v19 v20 ->
                                             coe
                                               MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942
                                               v15 v10
                                               (coe
                                                  du_cata'45'ev'45'alg'738'_36 (coe v15) (coe v20)
                                                  (coe
                                                     du_'10214'_'10215''738'_114
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                           (coe v15) (coe v14))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v17))
                                                        (coe v14))
                                                     (coe v11) (coe v3)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
                                               v19)))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_440 v10 v11
        -> case coe v1 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v12 v13 v14
               -> case coe v13 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v15 v16
                      -> case coe v14 of
                           MAlonzo.Code.Once.Type.C_ν'45'type_134 v17
                             -> coe
                                  (\ v18 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          (\ v19 v20 ->
                                             coe
                                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                               (coe
                                                  d_ana'45'events'738'_62 (coe v17) (coe v12)
                                                  (coe
                                                     du_'10214'_'10215''738'_114
                                                     (coe
                                                        MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                     (coe
                                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                        (coe v12)
                                                        (coe
                                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                           (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                           (coe v16))
                                                        (coe
                                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                           (coe v17) (coe v12)))
                                                     (coe v11) (coe v3)
                                                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                  (coe
                                                     MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                     (coe v12) (coe v19))
                                                  (coe v20))
                                               (coe
                                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                                  (coe v14)
                                                  (coe
                                                     MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026
                                                     (coe v17)
                                                     (coe
                                                        (\ v21 ->
                                                           coe
                                                             MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96
                                                             (coe v17)
                                                             (coe
                                                                MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                                (coe
                                                                   MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                   (coe v17) (coe v12))
                                                                (coe
                                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                                   (coe
                                                                      MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                                      (coe
                                                                         du_'10214'_'10215''738'_114
                                                                         (coe
                                                                            MAlonzo.Code.Once.Surface.Context.C_'8709'_8)
                                                                         (coe
                                                                            MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130
                                                                            (coe v12)
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                                               (coe
                                                                                  MAlonzo.Code.Once.Type.C_Many_10)
                                                                               (coe v16))
                                                                            (coe
                                                                               MAlonzo.Code.Once.Type.d_'10214'_'10215'T_166
                                                                               (coe v17) (coe v12)))
                                                                         (coe v11) (coe v3)
                                                                         (coe
                                                                            MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                                                      (0 :: Integer)
                                                                      (MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                                                         (coe v12) (coe v21)))
                                                                   (coe (0 :: Integer))))))
                                                     (coe
                                                        MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                                        (coe v12) (coe v19)))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
