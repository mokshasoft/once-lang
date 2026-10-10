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
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.String
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Empty
import qualified MAlonzo.Code.Data.Fin.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.SigOp.Builders
import qualified MAlonzo.Code.Once.CanonicalName
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.Sub
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.Float.Decimal
import qualified MAlonzo.Code.Once.Functor.Translate
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
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
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_cata'45'ev'45'alg'738'_36 v0 ~v1 v2 v3 v4
  = du_cata'45'ev'45'alg'738'_36 v0 v2 v3 v4
du_cata'45'ev'45'alg'738'_36 ::
  MAlonzo.Code.Once.Type.T_Functor_106 ->
  MAlonzo.Code.Once.Functor.Translate.T_WellFormedF_236 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_cata'45'ev'45'alg'738'_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.du_seqF_28 (coe v0)
         (coe v3))
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
              (coe v2)
              (coe
                 (\ v5 ->
                    coe
                      v5
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_460
                         (coe v0) (coe v1) (coe v4))))))
-- Once.Denotation.SourceDenote.liftD
d_liftD_58 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_liftD_58 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
      (MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_392
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Denotation.SourceDenote.DefsSem
d_DefsSem_70 = ()
data T_DefsSem_70
  = C_defsSem_88 MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6
                 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                  MAlonzo.Code.Once.Type.T_Type_108 ->
                  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178)
-- Once.Denotation.SourceDenote.DefsSem.calls
d_calls_80 ::
  T_DefsSem_70 -> MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6
d_calls_80 v0
  = case coe v0 of
      C_defsSem_88 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.SourceDenote.DefsSem.refs
d_refs_86 ::
  T_DefsSem_70 ->
  MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_refs_86 v0
  = case coe v0 of
      C_defsSem_88 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.SourceDenote.internalDefs
d_internalDefs_90 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 -> T_DefsSem_70
d_internalDefs_90 v0 v1
  = coe
      C_defsSem_88 (coe v1)
      (coe
         (\ v2 v3 ->
            MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
              (coe v0) (coe v1) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v3))
              (coe
                 MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v3)
                 (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v2)))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.Denotation.SourceDenote.sigOpˢ
d_sigOp'738'_104 ::
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  T_DefsSem_70 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_164 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_sigOp'738'_104 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_386
         (coe v1) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_184 (coe v4)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106 v2
         (MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe d_calls_80 (coe v3)))
         v0 v1 v4
         (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_356
            (coe v0) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_182 (coe v4))
            (coe v5)))
-- Once.Denotation.SourceDenote.⟦_⟧ˢ
d_'10214'_'10215''738'_122 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Surface.Context.T_Usage_60 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  T_DefsSem_70 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
d_'10214'_'10215''738'_122 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_'10214'_'10215''738'_122 v0 v1 v3 v4 v5 v6 v7
du_'10214'_'10215''738'_122 ::
  Integer ->
  MAlonzo.Code.Once.Surface.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  T_DefsSem_70 ->
  AgdaAny -> MAlonzo.Code.Once.Denotation.TraceMonad.T_T_178
du_'10214'_'10215''738'_122 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
             (coe
                MAlonzo.Code.Once.Denotation.Phase.du_lookup'7472'Used_12 (coe v1)
                (coe v9) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v10 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Type.C_Zero_6
                             -> coe
                                  seq (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                     (\ v22 ->
                                        coe
                                          du_'10214'_'10215''738'_122
                                          (coe addInt (coe (1 :: Integer)) (coe v0))
                                          (coe
                                             MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1)
                                             (coe v17))
                                          (coe v19) (coe v16) (coe v4) (coe v5) (coe v6)))
                           MAlonzo.Code.Once.Type.C_One_8
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5) (coe v6))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                 (coe v10) (coe v6) (coe v22)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Type.C_Many_10
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Type.C_Zero_6
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5) (coe v6))
                                  MAlonzo.Code.Once.Type.C_One_8
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                 (coe v10) (coe v6) (coe v22)))
                                  MAlonzo.Code.Once.Type.C_Many_10
                                    -> coe
                                         MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Surface.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                 (coe v10) (coe v6) (coe v22)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_app_50 v9 v10 v11 v13 v14 v15
        -> case coe v13 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v13)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v14) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                (coe v10)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                (coe v10)))
                          (coe v6)))
                    (coe
                       (\ v16 -> coe v16 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             MAlonzo.Code.Once.Type.C_One_8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v13)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v14) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                (coe v10)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                (coe v10)))
                          (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                       (coe
                          du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v11) (coe v15)
                          (coe v4) (coe v5)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                   (coe v10)))
                             (coe v10)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v13) (coe v10)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                   (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v13) (coe v10))))
                             (coe v6))))
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Type.C_mk'45'kind_50 (coe v13)
                             (coe MAlonzo.Code.Once.Type.C_pure_34))
                          (coe v2))
                       (coe v14) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                (coe v10)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                (coe v10)))
                          (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                       (coe
                          du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v11) (coe v15)
                          (coe v4) (coe v5)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                   (coe v10)))
                             (coe v10)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v13)
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v13) (coe v10)))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                   (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                      (coe v13) (coe v10))))
                             (coe v6))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_64 v9 v10 v11 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                    (\ v18 ->
                       coe
                         MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                         (coe
                            du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                            (coe
                               MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v11)
                               (coe
                                  MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                  (coe MAlonzo.Code.Once.Type.C_eff_36))
                               (coe v17))
                            (coe v13) (coe v4) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                               (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                  (coe v9)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                     (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                               (coe v6)))
                         (coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                            (coe
                               du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v11) (coe v14)
                               (coe v4) (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                  (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                        (coe v10))
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10))))
                                  (coe v6)))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_78 v9 v10 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'42'__124 v15 v16
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v15) (coe v13)
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                             (coe v10))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                             (coe v9) (coe v10))
                          (coe v6)))
                    (coe
                       (\ v17 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                            (coe
                               du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v16) (coe v14)
                               (coe v4) (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                     (coe v10))
                                  (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                     (coe v9) (coe v10))
                                  (coe v6)))
                            (coe
                               (\ v18 ->
                                  coe
                                    MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                       (coe v18))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_90 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v2) (coe v11))
                (coe v12) (coe v4) (coe v5) (coe v6))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                     (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v13))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_102 v10 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'42'__124 (coe v10) (coe v2))
                (coe v12) (coe v4) (coe v5) (coe v6))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                     (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v13))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_114 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v13) (coe v12)
                       (coe v4) (coe v5) (coe v6))
                    (coe
                       (\ v15 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v15))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_126 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'43'__126 v13 v14
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v14) (coe v12)
                       (coe v4) (coe v5) (coe v6))
                    (coe
                       (\ v15 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v15))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_148 v9 v10 v11 v12 v13 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C__'43'__126 (coe v14) (coe v15))
                (coe v17) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v10)
                         (coe v11)))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v10)
                         (coe v11)))
                   (coe v6)))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v20 ->
                   coe
                     du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v0))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v14))
                     (coe v2) (coe v18) (coe v4) (coe v5)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v12)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v10)
                              (coe v11))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''737'_428
                              (coe v10) (coe v11))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                    (coe v10) (coe v11)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v10)
                                 (coe v11))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                    (coe v10) (coe v11)))
                              (coe v6)))
                        (coe v20)))
                (\ v20 ->
                   coe
                     du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v0))
                     (coe
                        MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v15))
                     (coe v2) (coe v19) (coe v4) (coe v5)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v13)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v10)
                              (coe v11))
                           (coe v11)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''8852''691'_444
                              (coe v10) (coe v11))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                    (coe v10) (coe v11)))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140 (coe v10)
                                 (coe v11))
                              (coe
                                 MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'8852''7512'__140
                                    (coe v10) (coe v11)))
                              (coe v6)))
                        (coe v20))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_154
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_164 v11
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Void_122) (coe v11) (coe v4) (coe v5)
                (coe v6))
             (\ v12 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_180 v9 v10 v11 v12 v14 v15
        -> case coe v11 of
             MAlonzo.Code.Once.Type.C_Zero_6
               -> coe
                    du_'10214'_'10215''738'_122
                    (coe addInt (coe (1 :: Integer)) (coe v0))
                    (coe
                       MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v12))
                    (coe v2) (coe v15) (coe v4) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                             (coe v9)))
                       (coe v10)
                       (coe
                          MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                          (coe v10)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                             (coe v9)))
                       (coe v6))
             MAlonzo.Code.Once.Type.C_One_8
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v12) (coe v14)
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                (coe v9)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'One_390
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v9))))
                          (coe v6)))
                    (coe
                       (\ v16 ->
                          coe
                            du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v0))
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v12))
                            (coe v2) (coe v15) (coe v4) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v11)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v11) (coe v9)))
                                  (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v11) (coe v9)))
                                  (coe v6))
                               (coe v16))))
             MAlonzo.Code.Once.Type.C_Many_10
               -> coe
                    MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v12) (coe v14)
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                (coe v9)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128 (coe v11)
                                   (coe v9))))
                          (coe v6)))
                    (coe
                       (\ v16 ->
                          coe
                            du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v0))
                            (coe
                               MAlonzo.Code.Once.Surface.Context.du__'44'__16 (coe v1) (coe v12))
                            (coe v2) (coe v15) (coe v4) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v11)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v11) (coe v9)))
                                  (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                        (coe v11) (coe v9)))
                                  (coe v6))
                               (coe v16))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_186 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
             (MAlonzo.Code.Once.Word.d_fromℤ_20
                (coe MAlonzo.Code.Once.Target.Arch.d_int'45'bits_22 (coe v4))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_float_194 v9
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
             (MAlonzo.Code.Once.Float.Decimal.d_round_174
                (coe MAlonzo.Code.Once.Target.Arch.d_float'45'format_24 (coe v4))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_add_204 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_292)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_214 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_294)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_224 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_296)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_234 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136))
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_306)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_244 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136))
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_308)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_254 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136))
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_310)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_264 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Float_136)
                                (coe MAlonzo.Code.Once.Type.C_Float_136))
                             (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_312)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_272 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10) (coe v4) (coe v5)
                (coe v6))
             (coe
                d_sigOp'738'_104 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe MAlonzo.Code.Once.Type.C_Float_136) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_314))
      MAlonzo.Code.Once.Surface.Syntax.C_div_282 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_298)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_292 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_300)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_300 v10
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v10) (coe v4) (coe v5)
                (coe v6))
             (coe
                d_sigOp'738'_104 (coe MAlonzo.Code.Once.Type.C_Int_134)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_302))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_310 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe
                                MAlonzo.Code.Once.Type.C__'43'__126
                                (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                (coe MAlonzo.Code.Once.Type.C_Unit_120))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_316)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_320 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe
                                MAlonzo.Code.Once.Type.C__'43'__126
                                (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                (coe MAlonzo.Code.Once.Type.C_Unit_120))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_318)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_330 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe
                                MAlonzo.Code.Once.Type.C__'43'__126
                                (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                (coe MAlonzo.Code.Once.Type.C_Unit_120))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_320)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_340 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe
                                MAlonzo.Code.Once.Type.C__'43'__126
                                (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                (coe MAlonzo.Code.Once.Type.C_Unit_120))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_322)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_350 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe
                                MAlonzo.Code.Once.Type.C__'43'__126
                                (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                (coe MAlonzo.Code.Once.Type.C_Unit_120))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_324)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_360 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v11) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Type.C_Int_134) (coe v12) (coe v4) (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Type.C__'42'__124
                                (coe MAlonzo.Code.Once.Type.C_Int_134)
                                (coe MAlonzo.Code.Once.Type.C_Int_134))
                             (coe
                                MAlonzo.Code.Once.Type.C__'43'__126
                                (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                (coe MAlonzo.Code.Once.Type.C_Unit_120))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_326)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_372 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
             (coe
                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                (coe v10) (coe v2) (coe v12))
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v10) (coe v13)
                (coe v4) (coe v5) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_380 v10 v11
        -> let v12
                 = case coe v11 of
                     MAlonzo.Code.Once.Functor.Translate.C_con'45'base_226 v13
                       -> coe
                            d_sigOp'738'_104 (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v2)
                            (coe v4) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_332
                               (coe v10)
                               (coe MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
                               (coe v13))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Type.C_mk'45'kind_50 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.Type.C_Zero_6
                                -> case coe v17 of
                                     MAlonzo.Code.Once.Type.C_pure_34
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_234 v21 v22
                                              -> coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                                   (\ v23 ->
                                                      d_sigOp'738'_104
                                                        (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                        (coe v15) (coe v4) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_332
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
                                                           (coe v22))
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Functor.Translate.C_con'45'base_226 v19
                                              -> coe
                                                   d_sigOp'738'_104
                                                   (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v2)
                                                   (coe v4) (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_332
                                                      (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
                                                      (coe v19))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Type.C_eff_36
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_234 v21 v22
                                              -> coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                                   (\ v23 ->
                                                      d_sigOp'738'_104
                                                        (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                                        (coe v15) (coe v4) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
                                                           (coe v15) (coe v14) (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
                                                           (coe v22))
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Functor.Translate.C_con'45'base_226 v19
                                              -> coe
                                                   d_sigOp'738'_104
                                                   (coe MAlonzo.Code.Once.Type.C_Unit_120) (coe v2)
                                                   (coe v4) (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_332
                                                      (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
                                                      (coe v19))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_One_8
                                -> case coe v11 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_234 v21 v22
                                       -> coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                            (d_sigOp'738'_104
                                               (coe v13) (coe v15) (coe v4) (coe v5)
                                               (coe
                                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
                                                  (coe v15) (coe v14) (coe v10) (coe v21)
                                                  (coe v22)))
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'base_226 v19
                                       -> coe
                                            d_sigOp'738'_104 (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                            (coe v2) (coe v4) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_332
                                               (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
                                               (coe v19))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Type.C_Many_10
                                -> case coe v11 of
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'fun_234 v21 v22
                                       -> coe
                                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                            (d_sigOp'738'_104
                                               (coe v13) (coe v15) (coe v4) (coe v5)
                                               (coe
                                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_364
                                                  (coe v15) (coe v14) (coe v10) (coe v21)
                                                  (coe v22)))
                                     MAlonzo.Code.Once.Functor.Translate.C_con'45'base_226 v19
                                       -> coe
                                            d_sigOp'738'_104 (coe MAlonzo.Code.Once.Type.C_Unit_120)
                                            (coe v2) (coe v4) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_332
                                               (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Functor.Translate.C_base'45'Unit_198)
                                               (coe v19))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v12)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_388 v10
        -> coe
             MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v4)
             (coe d_calls_80 (coe v5)) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
             (coe
                MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v2)
                (coe MAlonzo.Code.Once.CanonicalName.d_bare_12 (coe v10)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_398 v9
        -> coe d_refs_86 v5 v9 v2
      MAlonzo.Code.Once.Surface.Syntax.C_closed_406 v10
        -> coe
             du_'10214'_'10215''738'_122 (coe (0 :: Integer))
             (coe MAlonzo.Code.Once.Surface.Context.C_'8709'_8) (coe v2)
             (coe v10) (coe v4) (coe v5)
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_418 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v13 v14 v15
               -> coe
                    d_liftD_58 (coe v4) (coe d_calls_80 (coe v5)) (coe v13) (coe v15)
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_430 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v10) (coe v13)
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                      (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                      (coe v9)
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                         (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9)))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                         (coe v9))
                      (coe
                         MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                         (coe MAlonzo.Code.Once.Surface.Context.d_zeroUsage_70 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9))))
                   (coe v6)))
             (coe
                (\ v14 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                     (coe v4) (coe d_calls_80 (coe v5))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v12)
                     (coe v14)))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_448 v9 v10 v12 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                           (coe
                              du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                 (coe v19))
                              (coe v15) (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116 (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                    (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                       (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                 (coe v6)))
                           (coe
                              (\ v22 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                   (coe
                                      du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v17)
                                         (coe
                                            MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                            (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                         (coe v12))
                                      (coe v16) (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                         (coe v10)
                                         (coe
                                            MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45'trans_376
                                            (coe v10)
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                               (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v10)))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                               (coe v10))
                                            (coe
                                               MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                                  (coe MAlonzo.Code.Once.Type.C_Many_10)
                                                  (coe v10))))
                                         (coe v6)))
                                   (coe
                                      (\ v23 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                           (\ v24 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                                (coe v23 v24) (coe v22))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_466 v9 v10 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
               -> case coe v17 of
                    MAlonzo.Code.Once.Type.C__'43'__126 v20 v21
                      -> case coe v18 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                        (coe v19))
                                     (coe v15) (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe v9) (coe v10))
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                           (coe v9) (coe v10))
                                        (coe v6)))
                                  (coe
                                     (\ v24 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                          (coe
                                             du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                                (coe v19))
                                             (coe v16) (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe v9) (coe v10))
                                                (coe v10)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                                   (coe v9) (coe v10))
                                                (coe v6)))
                                          (coe
                                             (\ v25 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v24 v25)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_484 v9 v10 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Type.C_mk'45'kind_50 v20 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Type.C__'42'__124 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                        (coe v22))
                                     (coe v15) (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                           (coe v9) (coe v10))
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''737'_322
                                           (coe v9) (coe v10))
                                        (coe v6)))
                                  (coe
                                     (\ v24 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                          (coe
                                             du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                                (coe v17)
                                                (coe
                                                   MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                                   (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v21))
                                                (coe v23))
                                             (coe v16) (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du__'43''7512'__116
                                                   (coe v9) (coe v10))
                                                (coe v10)
                                                (coe
                                                   MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''43''691'_338
                                                   (coe v9) (coe v10))
                                                (coe v6)))
                                          (coe
                                             (\ v25 ->
                                                coe
                                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                                  (\ v26 ->
                                                     coe
                                                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                                       (coe v24 v26)
                                                       (coe
                                                          (\ v27 ->
                                                             coe
                                                               MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                                               (coe v25 v26)
                                                               (coe
                                                                  (\ v28 ->
                                                                     coe
                                                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v27)
                                                                          (coe v28)))))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_502 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                        (coe
                                           MAlonzo.Code.Once.Type.C__'42'__124 (coe v16) (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v23))
                                        (coe v21))
                                     (coe v15) (coe v4) (coe v5) (coe v6))
                                  (coe
                                     (\ v24 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                          (\ v25 ->
                                             coe
                                               MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                               (\ v26 ->
                                                  coe
                                                    v24
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v25) (coe v26))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_516 v9 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Type.C_μ'45'type_130 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Type.C_mk'45'kind_50 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v18)
                                           (coe v17))
                                        (coe
                                           MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                        (coe v17))
                                     (coe v14) (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                           (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9))
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                           (coe v9))
                                        (coe v6)))
                                  (coe
                                     (\ v21 ->
                                        coe
                                          MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                          (coe
                                             MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_1080
                                             (coe v18) (coe v13)
                                             (coe
                                                du_cata'45'ev'45'alg'738'_36 (coe v18) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                                   v21)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_532 v9 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Type.C_ν'45'type_132 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__200
                           (coe
                              du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Type.C__'8658''91'_'93'__128 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Type.C_mk'45'kind_50
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v20))
                                 (coe
                                    MAlonzo.Code.Once.Type.d_'10214'_'10215'T_170 (coe v19)
                                    (coe v16)))
                              (coe v15) (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du__'42''7512'__128
                                    (coe MAlonzo.Code.Once.Type.C_Many_10) (coe v9))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Surface.Context.du_'8849''7512''45''42'Many_402
                                    (coe v9))
                                 (coe v6)))
                           (coe
                              (\ v21 ->
                                 coe
                                   MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                   (\ v22 ->
                                      coe
                                        MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_194
                                        (coe
                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_anaF'7496'_264
                                           v19
                                           (\ v23 ->
                                              coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_fmapT_238
                                                (coe
                                                   MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_418
                                                   (coe v19) (coe v14))
                                                (coe v21 v23))
                                           v22))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
