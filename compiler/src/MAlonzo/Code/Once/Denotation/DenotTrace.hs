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

module MAlonzo.Code.Once.Denotation.DenotTrace where

import MAlonzo.RTE (coe, erased, AgdaAny, addInt, subInt, mulInt,
                    quotInt, remInt, geqInt, ltInt, eqInt, add64, sub64, mul64, quot64,
                    rem64, lt64, eq64, word64FromNat, word64ToNat)
import qualified MAlonzo.RTE
import qualified Data.Text
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.Arith.Prim
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Internal.Iterative
import qualified MAlonzo.Code.Once.Internal.StreamInf
import qualified MAlonzo.Code.Once.Internal.Trace
import qualified MAlonzo.Code.Once.Internal.Value
import qualified MAlonzo.Code.Once.Res
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Spec.Float.Decimal
import qualified MAlonzo.Code.Once.Spec.Name
import qualified MAlonzo.Code.Once.Spec.Numerics
import qualified MAlonzo.Code.Once.Spec.Type
import qualified MAlonzo.Code.Once.Spec.Word

-- Once.Denotation.DenotTrace.CallEnv
d_CallEnv_6 = ()
data T_CallEnv_6
  = C_callEnv_24 (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
                  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58)
                 (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
                  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
                  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
                  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6)
-- Once.Denotation.DenotTrace.CallEnv.callsE
d_callsE_20 ::
  T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_callsE_20 v0
  = case coe v0 of
      C_callEnv_24 v1 v2 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.CallEnv.ffiE
d_ffiE_22 ::
  T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6
d_ffiE_22 v0
  = case coe v0 of
      C_callEnv_24 v1 v2 -> coe v2
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.sigOpSemT
d_sigOpSemT_32 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpSem_74 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110
d_sigOpSemT_32 v0 v1 v2 v3 v4 v5 v6
  = case coe v5 of
      MAlonzo.Code.Once.SigOp.Info.C_pureV_80 v7
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_ret_114
             (coe
                MAlonzo.Code.Once.Internal.Value.du_erase'7501'_110 (coe v3)
                (coe v7 v0 v6))
      MAlonzo.Code.Once.SigOp.Info.C_ffiV_82
        -> coe
             MAlonzo.Code.Once.Internal.Trace.du_resT_232
             (coe
                v1 (MAlonzo.Code.Once.SigOp.Info.d_name_110 (coe v4)) v2 v3 v6)
      MAlonzo.Code.Once.SigOp.Info.C_callsV_84
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_call_118
             (coe
                MAlonzo.Code.Once.Internal.Trace.C_callOp_74
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_110 (coe v4)) (coe v2)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4)) (coe v3))
             (coe v6) (coe MAlonzo.Code.Once.Internal.Trace.C_ret_114)
      MAlonzo.Code.Once.SigOp.Info.C_emitsV_86
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_call_118
             (coe
                MAlonzo.Code.Once.Internal.Trace.C_callOp_74
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_110 (coe v4)) (coe v2)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4))
                (coe MAlonzo.Code.Once.Spec.Type.C_Unit_18))
             (coe v6)
             (coe
                (\ v8 ->
                   coe
                     MAlonzo.Code.Once.Internal.Trace.C_ret_114
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)))
      MAlonzo.Code.Once.SigOp.Info.C_haltsV_88
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_halt_122
             (coe
                MAlonzo.Code.Once.Internal.Trace.C_haltOp_90
                (coe MAlonzo.Code.Once.SigOp.Info.d_name_110 (coe v4)) (coe v2)
                (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v4)))
             (coe v6)
      MAlonzo.Code.Once.SigOp.Info.C_primV_90 v7
        -> coe
             MAlonzo.Code.Once.Internal.Trace.C_ret_114
             (coe
                MAlonzo.Code.Once.Internal.Value.du_erase'7501'_110 (coe v3)
                (coe MAlonzo.Code.Once.Arith.Prim.du_primSem_238 v7 v0 v6))
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.sigOpT
d_sigOpT_106 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  (MAlonzo.Code.Once.Spec.Name.T_CanonicalName_6 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
   AgdaAny -> MAlonzo.Code.Once.Res.T_Res_6) ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.SigOp.Info.T_SigOpInfo_96 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Trace.T_T_110
d_sigOpT_106 v0 v1 v2 v3 v4
  = coe
      d_sigOpSemT_32 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
      (coe MAlonzo.Code.Once.SigOp.Info.d_sem_112 (coe v4))
-- Once.Denotation.DenotTrace.evalᴰ
d_eval'7472'_120 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_eval'7472'_120 v0 v1 v2 v3 v4 v5
  = case coe v4 of
      MAlonzo.Code.Once.IR.C_id_20
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70 (coe v5)
      MAlonzo.Code.Once.IR.C__'8728'__28 v7 v9 v10
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
             (coe
                d_eval'7472'_120 (coe v0) (coe v1) (coe v2) (coe v7) (coe v10)
                (coe v5))
             (coe d_eval'7472'_120 (coe v0) (coe v1) (coe v7) (coe v3) (coe v9))
      MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_36 v9 v10
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                    (coe
                       d_eval'7472'_120 (coe v0) (coe v1) (coe v2) (coe v11) (coe v9)
                       (coe v5))
                    (coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
                            (coe
                               d_eval'7472'_120 (coe v0) (coe v1) (coe v2) (coe v12) (coe v10)
                               (coe v5))
                            (coe
                               (\ v14 ->
                                  coe
                                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                       (coe v14))))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_fst_42
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
      MAlonzo.Code.Once.IR.C_snd_48
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
             (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
      MAlonzo.Code.Once.IR.C_inl_54
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v5))
      MAlonzo.Code.Once.IR.C_inr_60
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
             (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v5))
      MAlonzo.Code.Once.IR.C_case_68 v9 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
               -> case coe v5 of
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                      -> coe
                           d_eval'7472'_120 (coe v0) (coe v1) (coe v11) (coe v3) (coe v9)
                           (coe v13)
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                      -> coe
                           d_eval'7472'_120 (coe v0) (coe v1) (coe v12) (coe v3) (coe v10)
                           (coe v13)
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_terminal_72
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
             (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8)
      MAlonzo.Code.Once.IR.C_curry_84 v9
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                    (coe
                       (\ v12 ->
                          d_eval'7472'_120
                            (coe v0) (coe v1)
                            (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v2) (coe v10))
                            (coe v11) (coe v9)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v5) (coe v12))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_apply_90
        -> coe
             MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v5
             (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
      MAlonzo.Code.Once.IR.C_In_94 v7
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                    (coe
                       MAlonzo.Code.Once.Internal.Value.du_sem'45'In_542
                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8))
                       (coe
                          MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_248
                          (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8))
                          (coe
                             MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v8)
                             (coe v7))
                          (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_out'45'μ_98 v7
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                    (coe
                       MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_294
                       (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8))
                       (coe
                          MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v8)
                          (coe v7))
                       (coe
                          MAlonzo.Code.Once.Internal.Value.du_sem'45'Out_554
                          (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8))
                          (coe
                             MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v8)
                             (coe v7))
                          (coe v5)))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Cata_106 v7 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v12 of
                    MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v13
                      -> coe
                           MAlonzo.Code.Once.Internal.Value.du_sem'45'cata_570
                           (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v13))
                           (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                              (coe v13) (coe v7))
                           (d_cata'45'ev'45'alg'7472'_130
                              (coe v0) (coe v1) (coe v13) (coe v11) (coe v3) (coe v7) (coe v10)
                              (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5)))
                           (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Out_110 v7
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                    (coe
                       (\ v9 ->
                          coe
                            MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_294
                            (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8))
                            (coe
                               MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v8)
                               (coe v7))
                            (coe
                               MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'out_626
                               (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8))
                               (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                  (coe v8) (coe v7))
                               erased v9)))
                    (coe
                       MAlonzo.Code.Once.Internal.StreamInf.d_force'7477'_20 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_in'45'ν_114 v7
        -> case coe v3 of
             MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v8
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                    (coe
                       MAlonzo.Code.Once.Internal.StreamInf.du_in'45'ν'7477'_26
                       (coe
                          MAlonzo.Code.Once.Internal.Value.du_coerce'45'ν'45'in_616
                          (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8)) erased
                          (coe
                             MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_248
                             (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v8))
                             (coe
                                MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v8)
                                (coe v7))
                             (coe v5))))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Ana_122 v7 v10
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v11 v12
               -> case coe v3 of
                    MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v13
                      -> coe
                           MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                           (coe
                              MAlonzo.Code.Once.Internal.StreamInf.du_anaF'7477'_152
                              (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v13))
                              (\ v14 ->
                                 coe
                                   MAlonzo.Code.Once.Internal.Iterative.du_fmap'8734'_358
                                   (coe
                                      (\ v15 ->
                                         coe
                                           MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'45'D_248
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v13))
                                           (coe
                                              MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                                              (coe v13) (coe v7))
                                           (coe v15)))
                                   (coe
                                      d_eval'7472'_120 (coe v0) (coe v1) (coe v2)
                                      (coe
                                         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v13)
                                         (coe v12))
                                      (coe v10)
                                      (coe
                                         MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                                         (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                                         (coe v14))))
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5)))
                    _ -> MAlonzo.RTE.mazUnreachableError
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_Iter_130 v9
        -> case coe v2 of
             MAlonzo.Code.Once.IRTy.C__'42'__20 v10 v11
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_iter'8734'_256
                    (coe
                       (\ v12 ->
                          d_eval'7472'_120
                            (coe v0) (coe v1) (coe v2)
                            (coe MAlonzo.Code.Once.IRTy.C__'43'__22 (coe v3) (coe v11))
                            (coe v9)
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v5))
                               (coe v12))))
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_const_134 v7 v8
        -> case coe v7 of
             MAlonzo.Code.Once.IRTy.C_fits'45'int_516
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                    (coe
                       MAlonzo.Code.Once.Spec.Word.d_fromℤ_22
                       (coe MAlonzo.Code.Once.Spec.Numerics.d_int'45'bits_14 (coe v0))
                       (coe v8))
             MAlonzo.Code.Once.IRTy.C_fits'45'float_518
               -> coe
                    MAlonzo.Code.Once.Internal.Iterative.du_return'8734'_70
                    (coe
                       MAlonzo.Code.Once.Spec.Float.Decimal.d_round_176
                       (coe MAlonzo.Code.Once.Spec.Numerics.d_float'45'format_16 (coe v0))
                       (coe v8))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.IR.C_SigOp_140 v6 v7 v8
        -> coe
             MAlonzo.Code.Once.Internal.Iterative.du_embed_136
             (coe
                MAlonzo.Code.Once.Internal.Trace.du_fmapT_170
                (coe
                   (\ v9 ->
                      coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_inject'7495'_212
                        (coe v7) (coe MAlonzo.Code.Once.SigOp.Info.d_conB_116 (coe v8))
                        (coe v9)))
                (coe
                   d_sigOpT_106 v0 (d_ffiE_22 (coe v1)) v6 v7 v8
                   (coe
                      MAlonzo.Code.Once.Denotation.ValueDomain.du_forget'7495'_178
                      (coe v6) (coe MAlonzo.Code.Once.SigOp.Info.d_baseA_114 (coe v8))
                      (coe v5))))
      MAlonzo.Code.Once.IR.C_Call_146 v8
        -> coe d_callsE_20 v1 v8 v2 v3 v5
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.cata-ev-algᴰ
d_cata'45'ev'45'alg'7472'_130 ::
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_CallEnv_6 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_WellFormedFI_126 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_cata'45'ev'45'alg'7472'_130 v0 v1 v2 v3 v4 v5 v6 v7 v8
  = coe
      MAlonzo.Code.Once.Internal.Iterative.du__'62''62''61''8734'__78
      (coe
         MAlonzo.Code.Once.Internal.Iterative.du_seqF'8734'_372
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v2))
         (coe v8))
      (coe
         (\ v9 ->
            d_eval'7472'_120
              (coe v0) (coe v1)
              (coe
                 MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v3)
                 (coe
                    MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_84 (coe v2) (coe v4)))
              (coe v4) (coe v6)
              (coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v7)
                 (coe
                    MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_294
                    (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_582 (coe v2))
                    (coe
                       MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v2)
                       (coe v5))
                    (coe v9)))))
-- Once.Denotation.DenotTrace.liftFn
d_liftFn_404 ::
  Integer ->
  MAlonzo.Code.Once.Spec.Numerics.T_TargetNum_6 ->
  T_CallEnv_6 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.Spec.Type.T_Ty_8 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Once.Internal.Iterative.T_T'8734'_58
d_liftFn_404 v0 v1 v2 v3 v4 v5 v6
  = coe
      d_eval'7472'_120 (coe v1) (coe v2)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v3))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_50 (coe v0) (coe v4))
      (coe v5) (coe v6)
