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
import qualified MAlonzo.Code.Agda.Builtin.List
import qualified MAlonzo.Code.Agda.Builtin.Sigma
import qualified MAlonzo.Code.Agda.Builtin.Unit
import qualified MAlonzo.Code.Data.List.Base
import qualified MAlonzo.Code.Data.Sum.Base
import qualified MAlonzo.Code.Once.CCC.Eval
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Denotation.ValueDomain
import qualified MAlonzo.Code.Once.IR
import qualified MAlonzo.Code.Once.IRTy
import qualified MAlonzo.Code.Once.IRTy.WF
import qualified MAlonzo.Code.Once.Semantics.Value
import qualified MAlonzo.Code.Once.SigOp.Info
import qualified MAlonzo.Code.Once.Target.Arch
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.DenotTrace.evalᴰ
d_eval'7472'_12 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval'7472'_12 v0 v1 v2 v3 v4
  = let v5
          = \ v5 ->
              coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   d_rec'45'trace'45'D_20 (coe v0) (coe v1) (coe v2) (coe v3)
                   (coe
                      MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                      (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v1)) (coe v4))
                   (coe v5))
                (coe
                   MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                   (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v2))
                   (coe
                      MAlonzo.Code.Once.CCC.Eval.d_eval_12 (coe v1) (coe v2) (coe v0)
                      (coe v3)
                      (coe
                         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v1))
                         (coe v4)))) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C_id_22
           -> coe
                (\ v7 ->
                   coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12 (coe v4))
         MAlonzo.Code.Once.IR.C__'8728'__30 v7 v9 v10
           -> coe
                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                (coe d_eval'7472'_12 (coe v0) (coe v1) (coe v7) (coe v10) (coe v4))
                (coe d_eval'7472'_12 (coe v0) (coe v7) (coe v2) (coe v9))
         MAlonzo.Code.Once.IR.C_'10216'_'44'_'10217'_38 v9 v10 v11
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v12 v13
                  -> coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                       (coe d_eval'7472'_12 (coe v0) (coe v1) (coe v12) (coe v9) (coe v4))
                       (coe
                          (\ v14 ->
                             coe
                               MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                               (coe
                                  d_eval'7472'_12 (coe v0) (coe v1) (coe v13) (coe v10) (coe v4))
                               (coe
                                  (\ v15 v16 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v14)
                                          (coe v15))))))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_fst_44
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v4)))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_snd_50
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4)))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inl_56 v8
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
                  -> coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v4)))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_inr_62 v8
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v9 v10
                  -> coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v4)))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_case_70 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'43'__22 v11 v12
                  -> case coe v4 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v13
                         -> coe
                              d_eval'7472'_12 (coe v0) (coe v11) (coe v2) (coe v9) (coe v13)
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v13
                         -> coe
                              d_eval'7472'_12 (coe v0) (coe v12) (coe v2) (coe v10) (coe v13)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_terminal_74
           -> coe
                (\ v7 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         MAlonzo.Code.Once.IR.C_curry_86 v9 v10
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C__'8667'__24 v11 v12
                  -> coe
                       (\ v13 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe
                               (\ v14 ->
                                  d_eval'7472'_12
                                    (coe v0)
                                    (coe MAlonzo.Code.Once.IRTy.C__'42'__20 (coe v1) (coe v11))
                                    (coe v12) (coe v9)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v4)
                                       (coe v14)))))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_apply_92
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C__'42'__20 v8 v9
                  -> case coe v8 of
                       MAlonzo.Code.Once.IRTy.C__'8667'__24 v10 v11
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v4
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v4))
                       _ -> coe v5
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_Cata_106 v7 v9
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                  -> coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942
                            (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v10))
                            (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                               (coe v10) (coe v7))
                            (d_cata'45'ev'45'alg'7472'_28
                               (coe v0) (coe v10) (coe v2) (coe v11) (coe v9))
                            (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                               (coe
                                  MAlonzo.Code.Once.Type.C_μ'45'type_128
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v10)))
                               (coe v4)))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_Ana_126 v7 v9
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v10
                  -> coe
                       (\ v11 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               d_ana'45'events_44 (coe v0) (coe v10) (coe v1) (coe v9)
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v1))
                                  (coe v4))
                               (coe v11))
                            (coe
                               MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                               (coe
                                  MAlonzo.Code.Once.Type.C_ν'45'type_130
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v10)))
                               (coe
                                  MAlonzo.Code.Once.Semantics.Value.du_sem'45'ana_1026
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v10))
                                  (coe
                                     (\ v12 ->
                                        coe
                                          MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96
                                          (coe
                                             MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v10))
                                          (coe
                                             MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                             (coe
                                                MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                                                (coe
                                                   MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                   (coe v10) (coe v1)))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                (coe
                                                   d_eval'7472'_12 (coe v0) (coe v1)
                                                   (coe
                                                      MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                      (coe v10) (coe v1))
                                                   (coe v9)
                                                   (coe
                                                      MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                                      (coe
                                                         MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                                                         (coe v1))
                                                      (coe v12)))
                                                (coe (0 :: Integer))))))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                     (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v1))
                                     (coe v4)))))
                _ -> coe v5
         MAlonzo.Code.Once.IR.C_SigOp_154 v6 v7 v8
           -> coe
                (\ v9 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.du_emit'45'D_158 (coe v6)
                        (coe v8)
                        (coe
                           MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                           (coe
                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                              (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v6)))
                           (coe v4)))
                     (coe
                        MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60 (coe v7)
                        (coe
                           MAlonzo.Code.Once.SigOp.Info.du_semM_188 v8 v0
                           (MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                              (coe
                                 MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                                 (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v6)))
                              (coe v4)))))
         _ -> coe v5)
-- Once.Denotation.DenotTrace.rec-trace-D
d_rec'45'trace'45'D_20 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_rec'45'trace'45'D_20 v0 v1 v2 v3 v4 v5
  = let v6 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.IR.C_In_96 v8 v9
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v10
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_out'45'μ_100 v8
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v9
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_Cata_106 v8 v10
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_sem'45'cata_942
                          (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v11))
                          (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                             (coe v11) (coe v8))
                          (d_cata'45'ev'45'alg'7472'_28
                             (coe v0) (coe v11) (coe v2) (coe v5) (coe v10))
                          v4)
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_Para_112 v8 v10
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v11
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_sem'45'para_958
                          (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v11))
                          (coe
                             MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20 (coe v11)
                             (coe v8))
                          (coe
                             d_para'45'ev'45'alg'7472'_36 (coe v0) (coe v11) (coe v2) (coe v5)
                             (coe v10))
                          (coe v4))
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_Out_116 v8
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v9
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_Ana_126 v8 v10
           -> case coe v2 of
                MAlonzo.Code.Once.IRTy.C_ν'45'type_28 v11
                  -> coe
                       d_ana'45'events_44 (coe v0) (coe v11) (coe v1) (coe v10) (coe v4)
                       (coe v5)
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_Hylo_134 v7 v9 v10 v12 v13
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v14
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1252
                          (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v7))
                          (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v14))
                          (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                             (coe v7) (coe v9))
                          (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                             (coe v14) (coe v10))
                          (\ v15 v16 ->
                             coe
                               MAlonzo.Code.Once.CCC.Eval.du_appNatTr'45'F_22 (coe v14) (coe v7)
                               (coe v0) (coe v13) v16)
                          (\ v15 ->
                             coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                                  (coe
                                     d_eval'7472'_12 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                        (coe v2))
                                     (coe v2) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                              (coe v2)))
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v7))
                                           (coe v15))))
                                  (coe v5))
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v2))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        d_eval'7472'_12 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                           (coe v2))
                                        (coe v2) (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                 (coe v7) (coe v2)))
                                           (coe
                                              MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590
                                                 (coe v7))
                                              (coe v15))))
                                     (coe v5))))
                          v4)
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_Fuse_142 v7 v9 v10 v12 v13
           -> case coe v1 of
                MAlonzo.Code.Once.IRTy.C_μ'45'type_26 v14
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Value.du_sem'45'fuseNat'45'events_1252
                          (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
                          (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v7))
                          (MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v14))
                          (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                             (coe v7) (coe v9))
                          (MAlonzo.Code.Once.IRTy.WF.d_wf'45''8968''8969'_20
                             (coe v14) (coe v10))
                          (\ v15 v16 ->
                             coe
                               MAlonzo.Code.Once.CCC.Eval.du_appNatTr'45'F_22 (coe v14) (coe v7)
                               (coe v0) (coe v13) v16)
                          (\ v15 ->
                             coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                                  (coe
                                     d_eval'7472'_12 (coe v0)
                                     (coe
                                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                        (coe v2))
                                     (coe v2) (coe v12)
                                     (coe
                                        MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                              (coe v2)))
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v7))
                                           (coe v15))))
                                  (coe v5))
                               (coe
                                  MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
                                  (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v2))
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        d_eval'7472'_12 (coe v0)
                                        (coe
                                           MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v7)
                                           (coe v2))
                                        (coe v2) (coe v12)
                                        (coe
                                           MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                                           (coe
                                              MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68
                                                 (coe v7) (coe v2)))
                                           (coe
                                              MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
                                              (coe
                                                 MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590
                                                 (coe v7))
                                              (coe v15))))
                                     (coe v5))))
                          v4)
                _ -> coe v6
         MAlonzo.Code.Once.IR.C_free'45'heap_144 v7
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         MAlonzo.Code.Once.IR.C_const_148 v8 v9
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         _ -> coe v6)
-- Once.Denotation.DenotTrace.cata-ev-algᴰ
d_cata'45'ev'45'alg'7472'_28 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg'7472'_28 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10
            (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v1))
            (coe (\ v6 -> MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v6)))
            (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
            (coe
               d_eval'7472'_12 (coe v0)
               (coe
                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1) (coe v2))
               (coe v2) (coe v4) (coe du_z_338 (coe v1) (coe v5)))
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
         (coe
            d_eval'7472'_12 (coe v0)
            (coe
               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1) (coe v2))
            (coe v2) (coe v4) (coe du_z_338 (coe v1) (coe v5)))
         (coe v3))
-- Once.Denotation.DenotTrace.para-ev-algᴰ
d_para'45'ev'45'alg'7472'_36 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_para'45'ev'45'alg'7472'_36 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10
            (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v1))
            (coe
               (\ v6 ->
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v6))))
            (coe v5))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
            (coe
               d_eval'7472'_12 (coe v0)
               (coe
                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1)
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v1)) (coe v2)))
               (coe v2) (coe v4)
               (coe
                  MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                     (coe
                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1)
                        (coe
                           MAlonzo.Code.Once.IRTy.C__'42'__20
                           (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v1)) (coe v2))))
                  (coe du_z''_362 (coe v1) (coe v5))))
            (coe v3)))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v2))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe
               d_eval'7472'_12 (coe v0)
               (coe
                  MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1)
                  (coe
                     MAlonzo.Code.Once.IRTy.C__'42'__20
                     (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v1)) (coe v2)))
               (coe v2) (coe v4)
               (coe
                  MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
                  (coe
                     MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
                     (coe
                        MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1)
                        (coe
                           MAlonzo.Code.Once.IRTy.C__'42'__20
                           (coe MAlonzo.Code.Once.IRTy.C_μ'45'type_26 (coe v1)) (coe v2))))
                  (coe du_z''_362 (coe v1) (coe v5))))
            (coe v3)))
-- Once.Denotation.DenotTrace.ana-events
d_ana'45'events_44 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_118]
d_ana'45'events_44 v0 v1 v2 v3 v4 v5
  = case coe v5 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v6 = subInt (coe v5) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                   (coe du_step_390 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
                   (coe v6))
                (coe
                   MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10
                   (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v1))
                   (coe
                      (\ v7 ->
                         d_ana'45'events_44
                           (coe v0) (coe v1) (coe v2) (coe v3) (coe v7) (coe v6)))
                   (coe
                      d_layer_392 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4)
                      (coe v6))))
-- Once.Denotation.DenotTrace._.z
d_z_338 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_z_338 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_z_338 v1 v5
du_z_338 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> AgdaAny -> AgdaAny
du_z_338 v0 v1
  = coe
      MAlonzo.Code.Once.Denotation.ValueDomain.du_coerce'45'functor'8315''185''45'D_184
      (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v0))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v0))
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Denotation.DenotTrace._.z
d_z_358 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_z_358 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_z_358 v1 v5
du_z_358 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> AgdaAny -> AgdaAny
du_z_358 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor'8315''185'_138
      (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v0))
      (coe
         MAlonzo.Code.Once.Semantics.Value.du_sem'45'fmap_420
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v0))
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
         (coe v1))
-- Once.Denotation.DenotTrace._.z'
d_z''_362 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  Integer -> MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> AgdaAny
d_z''_362 ~v0 v1 ~v2 ~v3 ~v4 v5 = du_z''_362 v1 v5
du_z''_362 ::
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 -> AgdaAny -> AgdaAny
du_z''_362 v0 v1 = coe du_z_358 (coe v0) (coe v1)
-- Once.Denotation.DenotTrace._.step
d_step_390 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_390 v0 v1 v2 v3 v4 ~v5 = du_step_390 v0 v1 v2 v3 v4
du_step_390 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_390 v0 v1 v2 v3 v4
  = coe
      d_eval'7472'_12 (coe v0) (coe v2)
      (coe
         MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1) (coe v2))
      (coe v3)
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_inject_60
         (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588 (coe v2)) (coe v4))
-- Once.Denotation.DenotTrace._.layer
d_layer_392 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.IRTy.T_IRFunctor_4 ->
  MAlonzo.Code.Once.IRTy.T_IRTy_6 ->
  MAlonzo.Code.Once.IR.T_IR_16 -> AgdaAny -> Integer -> AgdaAny
d_layer_392 v0 v1 v2 v3 v4 v5
  = coe
      MAlonzo.Code.Once.Semantics.Value.du_coerce'45'functor_96
      (coe MAlonzo.Code.Once.IRTy.d_'8968'_'8969'F_590 (coe v1))
      (coe
         MAlonzo.Code.Once.Denotation.ValueDomain.d_forget_56
         (coe
            MAlonzo.Code.Once.IRTy.d_'8968'_'8969'_588
            (coe
               MAlonzo.Code.Once.IRTy.d_'10214'_'10215'TI_68 (coe v1) (coe v2)))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe du_step_390 (coe v0) (coe v1) (coe v2) (coe v3) (coe v4))
            (coe v5)))
-- Once.Denotation.DenotTrace.liftFn
d_liftFn_404 ::
  MAlonzo.Code.Once.Target.Arch.T_TargetNum_14 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.Type.T_Type_108 ->
  MAlonzo.Code.Once.IR.T_IR_16 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_liftFn_404 v0 v1 v2 v3 v4
  = coe
      d_eval'7472'_12 (coe v0)
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v1))
      (coe MAlonzo.Code.Once.IRTy.d_'8970'_'8971'_38 (coe v2)) (coe v3)
      (coe v4)
