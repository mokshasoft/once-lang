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
import qualified MAlonzo.Code.Once.Denotation.DenotTrace
import qualified MAlonzo.Code.Once.Denotation.Phase
import qualified MAlonzo.Code.Once.Denotation.Sub
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IR.Ref
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.Lang.Context
import qualified MAlonzo.Code.Once.Lang.Stream
import qualified MAlonzo.Code.Once.Lang.Trace
import qualified MAlonzo.Code.Once.Lang.Type
import qualified MAlonzo.Code.Once.Lang.Type.Grade
import qualified MAlonzo.Code.Once.Lang.Type.WellFormed
import qualified MAlonzo.Code.Once.Lang.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Word
import qualified MAlonzo.Code.Once.Surface.Syntax

-- Once.Denotation.SourceDenote.lookupᴰ
d_lookup'7472'_12 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
d_lookup'7472'_12 ~v0 v1 v2 v3 = du_lookup'7472'_12 v1 v2 v3
du_lookup'7472'_12 ::
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Data.Fin.Base.T_Fin_10 -> AgdaAny -> AgdaAny
du_lookup'7472'_12 v0 v1 v2
  = case coe v0 of
      MAlonzo.Code.Once.Lang.Context.C__'44'_'94'__12 v4 v5 v6
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
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_cata'45'ev'45'alg'738'_36 v0 ~v1 v2 v3 v4
  = du_cata'45'ev'45'alg'738'_36 v0 v2 v3 v4
du_cata'45'ev'45'alg'738'_36 ::
  MAlonzo.Code.Once.Lang.Type.T_Functor_6 ->
  MAlonzo.Code.Once.Lang.Type.WellFormed.T_WellFormedF_48 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_cata'45'ev'45'alg'738'_36 v0 v1 v2 v3
  = coe
      MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
      (coe MAlonzo.Code.Once.Lang.Stream.du_seqF_34 (coe v0) (coe v3))
      (coe
         (\ v4 ->
            coe
              MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132 (coe v2)
              (coe
                 (\ v5 ->
                    coe
                      v5
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_274
                         (coe v0) (coe v1) (coe v4))))))
-- Once.Denotation.SourceDenote.liftD
d_liftD_58 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
d_liftD_58 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Lang.Trace.du_returnT_126
      (MAlonzo.Code.Once.Denotation.DenotTrace.d_liftFn_392
         (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
-- Once.Denotation.SourceDenote.DefsSem
d_DefsSem_70 = ()
data T_DefsSem_70
  = C_defsSem_88 MAlonzo.Code.Once.Denotation.DenotTrace.T_CallEnv_6
                 (MAlonzo.Code.Agda.Builtin.String.T_String_6 ->
                  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
                  MAlonzo.Code.Once.Lang.Trace.T_T_110)
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
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Trace.T_T_110
d_refs_86 v0
  = case coe v0 of
      C_defsSem_88 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.SourceDenote.internalDefs
d_internalDefs_90 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
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
                 (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v2)))
              (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
-- Once.Denotation.SourceDenote.sigOpˢ
d_sigOp'738'_104 ::
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_DefsSem_70 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_sigOp'738'_104 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_inject'7495'_200
         (coe v1) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v4)))
      (coe
         MAlonzo.Code.Once.Denotation.DenotTrace.d_sigOpT_106 v2
         (MAlonzo.Code.Once.Denotation.DenotTrace.d_ffiE_22
            (coe d_calls_80 (coe v3)))
         v0 v1 v4
         (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget'7495'_170
            (coe v0) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
            (coe v5)))
-- Once.Denotation.SourceDenote.⟦_⟧ˢ
d_'10214'_'10215''738'_122 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Context.T_Usage_46 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_DefsSem_70 -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
d_'10214'_'10215''738'_122 v0 v1 ~v2 v3 v4 v5 v6 v7
  = du_'10214'_'10215''738'_122 v0 v1 v3 v4 v5 v6 v7
du_'10214'_'10215''738'_122 ::
  Integer ->
  MAlonzo.Code.Once.Lang.Context.T_Ctx_6 ->
  MAlonzo.Code.Once.Lang.Type.T_Type_8 ->
  MAlonzo.Code.Once.Surface.Syntax.T_Expr_8 ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_DefsSem_70 -> AgdaAny -> MAlonzo.Code.Once.Lang.Trace.T_T_110
du_'10214'_'10215''738'_122 v0 v1 v2 v3 v4 v5 v6
  = case coe v3 of
      MAlonzo.Code.Once.Surface.Syntax.C_var_16 v9
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du_returnT_126
             (coe
                MAlonzo.Code.Once.Denotation.Phase.du_lookup'7472'Used_12 (coe v1)
                (coe v9) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_lam_34 v10 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                             -> coe
                                  seq (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                     (\ v22 ->
                                        coe
                                          du_'10214'_'10215''738'_122
                                          (coe addInt (coe (1 :: Integer)) (coe v0))
                                          (coe
                                             MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1)
                                             (coe v17))
                                          (coe v19) (coe v16) (coe v4) (coe v5) (coe v6)))
                           MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5) (coe v6))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                 (coe v10) (coe v6) (coe v22)))
                                  _ -> MAlonzo.RTE.mazUnreachableError
                           MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                             -> case coe v10 of
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5) (coe v6))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'44'__16
                                                 (coe v1) (coe v17))
                                              (coe v19) (coe v16) (coe v4) (coe v5)
                                              (coe
                                                 MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114
                                                 (coe v10) (coe v6) (coe v22)))
                                  MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                    -> coe
                                         MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                         (\ v22 ->
                                            coe
                                              du_'10214'_'10215''738'_122
                                              (coe addInt (coe (1 :: Integer)) (coe v0))
                                              (coe
                                                 MAlonzo.Code.Once.Lang.Context.du__'44'__16
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
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v13)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v2))
                       (coe v14) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                (coe v10)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                (coe v10)))
                          (coe v6)))
                    (coe
                       (\ v16 -> coe v16 (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v13)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v2))
                       (coe v14) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                (coe v10)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                (coe v10)))
                          (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                       (coe
                          du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v11) (coe v15)
                          (coe v4) (coe v5)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                   (coe v10)))
                             (coe v10)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                      (coe v10)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'One_292
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                   (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                      (coe v10))))
                             (coe v6))))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                       (coe
                          MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                          (coe
                             MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 (coe v13)
                             (coe MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34))
                          (coe v2))
                       (coe v14) (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                (coe v10)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                (coe v10)))
                          (coe v6)))
                    (coe
                       MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                       (coe
                          du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v11) (coe v15)
                          (coe v4) (coe v5)
                          (coe
                             MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                   (coe v10)))
                             (coe v10)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                      (coe v10)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                   (coe v10))
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                   (coe v9)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v13)
                                      (coe v10))))
                             (coe v6))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_effApp_68 v9 v10 v11 v14 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                           (\ v22 ->
                              coe
                                MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                (coe
                                   du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                   (coe
                                      MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v11)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                         (coe v21))
                                      (coe v19))
                                   (coe v15) (coe v4) (coe v5)
                                   (coe
                                      MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                      (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v10)))
                                      (coe v9)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                         (coe v9)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v10)))
                                      (coe v6)))
                                (coe
                                   MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                   (coe
                                      du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v11)
                                      (coe v16) (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v10)))
                                         (coe v10)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                            (coe v10)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v10))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v10)))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                               (coe v10))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v10))))
                                         (coe v6)))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_pair_82 v9 v10 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'42'__24 v15 v16
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v15) (coe v13)
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                             (coe v10))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                             (coe v9) (coe v10))
                          (coe v6)))
                    (coe
                       (\ v17 ->
                          coe
                            MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                            (coe
                               du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v16) (coe v14)
                               (coe v4) (coe v5)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                     (coe v10))
                                  (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                     (coe v9) (coe v10))
                                  (coe v6)))
                            (coe
                               (\ v18 ->
                                  coe
                                    MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v17)
                                       (coe v18))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fst''_94 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v2) (coe v11))
                (coe v12) (coe v4) (coe v5) (coe v6))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                     (MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v13))))
      MAlonzo.Code.Once.Surface.Syntax.C_snd''_106 v10 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v10) (coe v2))
                (coe v12) (coe v4) (coe v5) (coe v6))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                     (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v13))))
      MAlonzo.Code.Once.Surface.Syntax.C_inl''_118 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v13) (coe v12)
                       (coe v4) (coe v5) (coe v6))
                    (coe
                       (\ v15 ->
                          coe
                            MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v15))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_inr''_130 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'43'__26 v13 v14
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v14) (coe v12)
                       (coe v4) (coe v5) (coe v6))
                    (coe
                       (\ v15 ->
                          coe
                            MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v15))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_case''_152 v9 v10 v11 v12 v13 v14 v15 v17 v18 v19
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C__'43'__26 (coe v14) (coe v15))
                (coe v17) (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                         (coe v11)))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                         (coe v11)))
                   (coe v6)))
             (coe
                MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                (\ v20 ->
                   coe
                     du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v0))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v14))
                     (coe v2) (coe v18) (coe v4) (coe v5)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v12)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                              (coe v11))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''737'_330
                              (coe v10) (coe v11))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                                    (coe v11)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                                 (coe v11))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                                    (coe v11)))
                              (coe v6)))
                        (coe v20)))
                (\ v20 ->
                   coe
                     du_'10214'_'10215''738'_122
                     (coe addInt (coe (1 :: Integer)) (coe v0))
                     (coe
                        MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v15))
                     (coe v2) (coe v19) (coe v4) (coe v5)
                     (coe
                        MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v13)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                              (coe v11))
                           (coe v11)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''8852''691'_346
                              (coe v10) (coe v11))
                           (coe
                              MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                                    (coe v11)))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                                 (coe v11))
                              (coe
                                 MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'8852''7512'__100 (coe v10)
                                    (coe v11)))
                              (coe v6)))
                        (coe v20))))
      MAlonzo.Code.Once.Surface.Syntax.C_unit_158
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du_returnT_126
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_absurd_168 v11
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Void_22) (coe v11) (coe v4)
                (coe v5) (coe v6))
             (\ v12 -> coe MAlonzo.Code.Data.Empty.du_'8869''45'elim_12)
      MAlonzo.Code.Once.Surface.Syntax.C_let''_184 v9 v10 v11 v12 v14 v15
        -> case coe v11 of
             MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
               -> coe
                    du_'10214'_'10215''738'_122
                    (coe addInt (coe (1 :: Integer)) (coe v0))
                    (coe
                       MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v12))
                    (coe v2) (coe v15) (coe v4) (coe v5)
                    (coe
                       MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v10)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                             (coe v9)))
                       (coe v10)
                       (coe
                          MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                          (coe v10)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                             (coe v9)))
                       (coe v6))
             MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v12) (coe v14)
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                (coe v9)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'One_292
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v9))))
                          (coe v6)))
                    (coe
                       (\ v16 ->
                          coe
                            du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v0))
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v12))
                            (coe v2) (coe v15) (coe v4) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v11)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                        (coe v9)))
                                  (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                        (coe v9)))
                                  (coe v6))
                               (coe v16))))
             MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
               -> coe
                    MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                    (coe
                       du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v12) (coe v14)
                       (coe v4) (coe v5)
                       (coe
                          MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v10)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                (coe v9)))
                          (coe v9)
                          (coe
                             MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                             (coe v9)
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v9)))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                (coe v9))
                             (coe
                                MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                (coe v10)
                                (coe
                                   MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                   (coe v9))))
                          (coe v6)))
                    (coe
                       (\ v16 ->
                          coe
                            du_'10214'_'10215''738'_122
                            (coe addInt (coe (1 :: Integer)) (coe v0))
                            (coe
                               MAlonzo.Code.Once.Lang.Context.du__'44'__16 (coe v1) (coe v12))
                            (coe v2) (coe v15) (coe v4) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Denotation.Phase.du_bind'7472'_114 (coe v11)
                               (coe
                                  MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                        (coe v9)))
                                  (coe v10)
                                  (coe
                                     MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                     (coe v10)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88 (coe v11)
                                        (coe v9)))
                                  (coe v6))
                               (coe v16))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_int_190 v9
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du_returnT_126
             (MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
                (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v4))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_float_198 v9
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du_returnT_126
             (MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
                (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v4))
                (coe v9))
      MAlonzo.Code.Once.Surface.Syntax.C_add_208 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_add'45'info_114)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_sub_218 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_sub'45'info_116)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mul_228 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mul'45'info_118)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fadd_238 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fadd'45'info_128)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fsub_248 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fsub'45'info_130)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fmul_258 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fmul'45'info_132)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_fdiv_268 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_fdiv'45'info_134)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_i2f_276 v10
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10) (coe v4)
                (coe v5) (coe v6))
             (coe
                d_sigOp'738'_104 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe MAlonzo.Code.Once.Lang.Type.C_Float_36) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_i2f'45'info_136))
      MAlonzo.Code.Once.Surface.Syntax.C_div_286 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_div'45'info_120)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_mod''_296 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_mod'45'info_122)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_neg_304 v10
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v10) (coe v4)
                (coe v5) (coe v6))
             (coe
                d_sigOp'738'_104 (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v4) (coe v5)
                (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_neg'45'info_124))
      MAlonzo.Code.Once.Surface.Syntax.C_lt_314 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_lt'45'info_138)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_le_324 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_le'45'info_140)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_gt_334 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_gt'45'info_142)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ge_344 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ge'45'info_144)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_eq_354 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_eq'45'info_146)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_ne_364 v9 v10 v11 v12
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v11) (coe v4)
                (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                      (coe v10))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                      (coe v9) (coe v10))
                   (coe v6)))
             (coe
                (\ v13 ->
                   coe
                     MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                     (coe
                        du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                        (coe MAlonzo.Code.Once.Lang.Type.C_Int_34) (coe v12) (coe v4)
                        (coe v5)
                        (coe
                           MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                              (coe v10))
                           (coe v10)
                           (coe
                              MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                              (coe v9) (coe v10))
                           (coe v6)))
                     (coe
                        (\ v14 ->
                           d_sigOp'738'_104
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'42'__24
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Int_34))
                             (coe
                                MAlonzo.Code.Once.Lang.Type.C__'43'__26
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20))
                             (coe v4) (coe v5)
                             (coe MAlonzo.Code.Once.Arith.SigOp.Builders.d_ne'45'info_148)
                             (coe
                                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                (coe v14))))))
      MAlonzo.Code.Once.Surface.Syntax.C_coerce_376 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
             (coe
                MAlonzo.Code.Once.Denotation.Sub.d_'10214'_'10215''60''58'_10
                (coe v10) (coe v2) (coe v12))
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v10) (coe v13)
                (coe v4) (coe v5) (coe v6))
      MAlonzo.Code.Once.Surface.Syntax.C_sigOp_384 v10 v11
        -> let v12
                 = case coe v11 of
                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v13
                       -> coe
                            d_sigOp'738'_104 (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                            (coe v2) (coe v4) (coe v5)
                            (coe
                               MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                               (coe v10)
                               (coe MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                               (coe v13))
                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                     _ -> MAlonzo.RTE.mazUnreachableError in
           coe
             (case coe v2 of
                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
                  -> case coe v14 of
                       MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v16 v17
                         -> case coe v16 of
                              MAlonzo.Code.Once.Lang.Type.Grade.C_Zero_10
                                -> case coe v17 of
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_pure_34
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v21 v22
                                              -> coe
                                                   MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                                   (\ v23 ->
                                                      d_sigOp'738'_104
                                                        (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                        (coe v15) (coe v4) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                           (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                           (coe v22))
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                                              -> coe
                                                   d_sigOp'738'_104
                                                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                   (coe v2) (coe v4) (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                      (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                      (coe v19))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_act_36
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v21 v22
                                              -> coe
                                                   MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                                   (\ v23 ->
                                                      d_sigOp'738'_104
                                                        (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                        (coe v15) (coe v4) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                           (coe v15) (coe v14) (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                           (coe v22))
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                                              -> coe
                                                   d_sigOp'738'_104
                                                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                   (coe v2) (coe v4) (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                      (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                      (coe v19))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     MAlonzo.Code.Once.Lang.Type.Grade.C_eff_38
                                       -> case coe v11 of
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v21 v22
                                              -> coe
                                                   MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                                   (\ v23 ->
                                                      d_sigOp'738'_104
                                                        (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                        (coe v15) (coe v4) (coe v5)
                                                        (coe
                                                           MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                           (coe v15) (coe v14) (coe v10)
                                                           (coe
                                                              MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                           (coe v22))
                                                        (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
                                            MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                                              -> coe
                                                   d_sigOp'738'_104
                                                   (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20)
                                                   (coe v2) (coe v4) (coe v5)
                                                   (coe
                                                      MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                                      (coe v10)
                                                      (coe
                                                         MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                                      (coe v19))
                                                   (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                            _ -> MAlonzo.RTE.mazUnreachableError
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Lang.Type.Grade.C_One_12
                                -> case coe v11 of
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v21 v22
                                       -> coe
                                            MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                            (d_sigOp'738'_104
                                               (coe v13) (coe v15) (coe v4) (coe v5)
                                               (coe
                                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                  (coe v15) (coe v14) (coe v10) (coe v21)
                                                  (coe v22)))
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                                       -> coe
                                            d_sigOp'738'_104
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v2)
                                            (coe v4) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                               (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                               (coe v19))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14
                                -> case coe v11 of
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'fun_46 v21 v22
                                       -> coe
                                            MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                            (d_sigOp'738'_104
                                               (coe v13) (coe v15) (coe v4) (coe v5)
                                               (coe
                                                  MAlonzo.Code.Once.Arith.SigOp.Builders.du_arrow'45'info_188
                                                  (coe v15) (coe v14) (coe v10) (coe v21)
                                                  (coe v22)))
                                     MAlonzo.Code.Once.Lang.Type.WellFormed.C_con'45'base_38 v19
                                       -> coe
                                            d_sigOp'738'_104
                                            (coe MAlonzo.Code.Once.Lang.Type.C_Unit_20) (coe v2)
                                            (coe v4) (coe v5)
                                            (coe
                                               MAlonzo.Code.Once.Arith.SigOp.Builders.du_value'45'info_154
                                               (coe v10)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Type.WellFormed.C_base'45'Unit_10)
                                               (coe v19))
                                            (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
                                     _ -> MAlonzo.RTE.mazUnreachableError
                              _ -> MAlonzo.RTE.mazUnreachableError
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v12)
      MAlonzo.Code.Once.Surface.Syntax.C_closure_392 v10
        -> coe
             MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120 (coe v4)
             (coe d_calls_80 (coe v5)) (coe MAlonzo.Code.Once.IRTy.C_Unit_16)
             (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2))
             (coe
                MAlonzo.Code.Once.IR.Ref.d_refIR_8 (coe v2)
                (coe MAlonzo.Code.Once.Spec.Name.d_bare_14 (coe v10)))
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_poly_402 v9
        -> coe d_refs_86 v5 v9 v2
      MAlonzo.Code.Once.Surface.Syntax.C_closed_410 v10
        -> coe
             du_'10214'_'10215''738'_122 (coe (0 :: Integer))
             (coe MAlonzo.Code.Once.Lang.Context.C_'8709'_8) (coe v2) (coe v10)
             (coe v4) (coe v5) (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.Surface.Syntax.C_lift'45'morphism_422 v12
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v13 v14 v15
               -> coe
                    d_liftD_58 (coe v4) (coe d_calls_80 (coe v5)) (coe v13) (coe v15)
                    (coe v12)
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_morph'45'app_434 v9 v10 v12 v13
        -> coe
             MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
             (coe
                du_'10214'_'10215''738'_122 (coe v0) (coe v1) (coe v10) (coe v13)
                (coe v4) (coe v5)
                (coe
                   MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                      (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9)))
                   (coe v9)
                   (coe
                      MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                      (coe v9)
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                         (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9)))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                         (coe v9))
                      (coe
                         MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                         (coe MAlonzo.Code.Once.Lang.Context.d_zeroUsage_56 (coe v0))
                         (coe
                            MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9))))
                   (coe v6)))
             (coe
                (\ v14 ->
                   MAlonzo.Code.Once.Denotation.DenotTrace.d_eval'7472'_120
                     (coe v4) (coe d_calls_80 (coe v5))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v10))
                     (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_48 (coe v2)) (coe v12)
                     (coe v14)))
      MAlonzo.Code.Once.Surface.Syntax.C_comp''_452 v9 v10 v12 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v20 v21
                      -> coe
                           MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                           (coe
                              du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v12)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v21))
                                 (coe v19))
                              (coe v15) (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76 (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v10)))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                    (coe v9)
                                    (coe
                                       MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                       (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v10)))
                                 (coe v6)))
                           (coe
                              (\ v22 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                   (coe
                                      du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                      (coe
                                         MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                         (coe v17)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                            (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                            (coe v21))
                                         (coe v12))
                                      (coe v16) (coe v4) (coe v5)
                                      (coe
                                         MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                         (coe v1)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                            (coe v9)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v10)))
                                         (coe v10)
                                         (coe
                                            MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45'trans_278
                                            (coe v10)
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                               (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                               (coe v10))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v10)))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                               (coe v10))
                                            (coe
                                               MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                               (coe v9)
                                               (coe
                                                  MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                                  (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                  (coe v10))))
                                         (coe v6)))
                                   (coe
                                      (\ v23 ->
                                         coe
                                           MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                           (\ v24 ->
                                              coe
                                                MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                                (coe v23 v24) (coe v22))))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_copair''_470 v9 v10 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> case coe v17 of
                    MAlonzo.Code.Once.Lang.Type.C__'43'__26 v20 v21
                      -> case coe v18 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v20)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v23))
                                        (coe v19))
                                     (coe v15) (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                           (coe v9) (coe v10))
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                           (coe v9) (coe v10))
                                        (coe v6)))
                                  (coe
                                     (\ v24 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                          (coe
                                             du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v21)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v23))
                                                (coe v19))
                                             (coe v16) (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                   (coe v9) (coe v10))
                                                (coe v10)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v9) (coe v10))
                                                (coe v6)))
                                          (coe
                                             (\ v25 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                                  (coe
                                                     MAlonzo.Code.Data.Sum.Base.du_'91'_'44'_'93''8242'_66
                                                     v24 v25)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_fork''_488 v9 v10 v15 v16
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v17 v18 v19
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v20 v21
                      -> case coe v19 of
                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v17)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v21))
                                        (coe v22))
                                     (coe v15) (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                           (coe v9) (coe v10))
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''737'_224
                                           (coe v9) (coe v10))
                                        (coe v6)))
                                  (coe
                                     (\ v24 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                          (coe
                                             du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                             (coe
                                                MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                                (coe v17)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                                   (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                                   (coe v21))
                                                (coe v23))
                                             (coe v16) (coe v4) (coe v5)
                                             (coe
                                                MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                                (coe v1)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du__'43''7512'__76
                                                   (coe v9) (coe v10))
                                                (coe v10)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''43''691'_240
                                                   (coe v9) (coe v10))
                                                (coe v6)))
                                          (coe
                                             (\ v25 ->
                                                coe
                                                  MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                                  (\ v26 ->
                                                     coe
                                                       MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                                       (coe v24 v26)
                                                       (coe
                                                          (\ v27 ->
                                                             coe
                                                               MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                                               (coe v25 v26)
                                                               (coe
                                                                  (\ v28 ->
                                                                     coe
                                                                       MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                                                       (coe
                                                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                                          (coe v27)
                                                                          (coe v28)))))))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_curry''_506 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v19 v20 v21
                      -> case coe v20 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v22 v23
                             -> coe
                                  MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.C__'42'__24 (coe v16)
                                           (coe v19))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v23))
                                        (coe v21))
                                     (coe v15) (coe v4) (coe v5) (coe v6))
                                  (coe
                                     (\ v24 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                          (\ v25 ->
                                             coe
                                               MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                               (\ v26 ->
                                                  coe
                                                    v24
                                                    (coe
                                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                                       (coe v25) (coe v26))))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_cata_520 v9 v13 v14
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v15 v16 v17
               -> case coe v15 of
                    MAlonzo.Code.Once.Lang.Type.C_μ'45'type_30 v18
                      -> case coe v16 of
                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70 v19 v20
                             -> coe
                                  MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                                  (coe
                                     du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                                     (coe
                                        MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62
                                           (coe v18) (coe v17))
                                        (coe
                                           MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v20))
                                        (coe v17))
                                     (coe v14) (coe v4) (coe v5)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40
                                        (coe v1)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                           (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14)
                                           (coe v9))
                                        (coe v9)
                                        (coe
                                           MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                           (coe v9))
                                        (coe v6)))
                                  (coe
                                     (\ v21 ->
                                        coe
                                          MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                          (coe
                                             MAlonzo.Code.Once.Lang.Value.du_sem'45'cata_538
                                             (coe v18) (coe v13)
                                             (coe
                                                du_cata'45'ev'45'alg'738'_36 (coe v18) (coe v13)
                                                (coe
                                                   MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                                   v21)))))
                           _ -> MAlonzo.RTE.mazUnreachableError
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Surface.Syntax.C_ana_536 v9 v14 v15
        -> case coe v2 of
             MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 v16 v17 v18
               -> case coe v18 of
                    MAlonzo.Code.Once.Lang.Type.C_ν'45'type_32 v19 v20
                      -> coe
                           MAlonzo.Code.Once.Lang.Trace.du__'62''62''61'T__132
                           (coe
                              du_'10214'_'10215''738'_122 (coe v0) (coe v1)
                              (coe
                                 MAlonzo.Code.Once.Lang.Type.C__'8658''91'_'93'__28 (coe v16)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.Grade.C_mk'45'kind_70
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v20))
                                 (coe
                                    MAlonzo.Code.Once.Lang.Type.d_'10214'_'10215'T_62 (coe v19)
                                    (coe v16)))
                              (coe v15) (coe v4) (coe v5)
                              (coe
                                 MAlonzo.Code.Once.Denotation.Phase.du_restrict'7472'_40 (coe v1)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du__'42''7512'__88
                                    (coe MAlonzo.Code.Once.Lang.Type.Grade.C_Many_14) (coe v9))
                                 (coe v9)
                                 (coe
                                    MAlonzo.Code.Once.Lang.Context.du_'8849''7512''45''42'Many_304
                                    (coe v9))
                                 (coe v6)))
                           (coe
                              (\ v21 ->
                                 coe
                                   MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                   (\ v22 ->
                                      coe
                                        MAlonzo.Code.Once.Lang.Trace.du_returnT_126
                                        (coe
                                           MAlonzo.Code.Once.Lang.Stream.du_anaF'7496'_168 v19
                                           (\ v23 ->
                                              coe
                                                MAlonzo.Code.Once.Lang.Trace.du_fmapT_170
                                                (coe
                                                   MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_232
                                                   (coe v19) (coe v14))
                                                (coe v21 v23))
                                           v22))))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      _ -> MAlonzo.RTE.mazUnreachableError
