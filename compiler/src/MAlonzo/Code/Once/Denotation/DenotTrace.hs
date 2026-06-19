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
import qualified MAlonzo.Code.Once.CCC.IR
import qualified MAlonzo.Code.Once.CCC.SigOp.Info
import qualified MAlonzo.Code.Once.Denotation.Trace
import qualified MAlonzo.Code.Once.Denotation.TraceDenote
import qualified MAlonzo.Code.Once.Denotation.TraceMonad
import qualified MAlonzo.Code.Once.Semantics.Core
import qualified MAlonzo.Code.Once.Type

-- Once.Denotation.DenotTrace.⟦_⟧ᴰ
d_'10214'_'10215''7472'_6 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> ()
d_'10214'_'10215''7472'_6 = erased
-- Once.Denotation.DenotTrace.forget
d_forget_26 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_forget_26 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_forget_26 (coe v2) (coe v4))
                    (coe d_forget_26 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_forget_26 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_forget_26 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
        -> coe
             (\ v5 ->
                d_forget_26
                  (coe v4)
                  (coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                     (coe v1 (d_inject_30 (coe v2) (coe v5))) (coe (0 :: Integer))))
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Int_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_138 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_140 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_142 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.inject
d_inject_30 ::
  MAlonzo.Code.Once.Type.T_Type_112 -> AgdaAny -> AgdaAny
d_inject_30 v0 v1
  = case coe v0 of
      MAlonzo.Code.Once.Type.C_Unit_122 -> coe v1
      MAlonzo.Code.Once.Type.C__'42'__126 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 v4 v5
               -> coe
                    MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                    (coe d_inject_30 (coe v2) (coe v4))
                    (coe d_inject_30 (coe v3) (coe v5))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'43'__128 v2 v3
        -> case coe v1 of
             MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38
                    (coe d_inject_30 (coe v2) (coe v4))
             MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v4
               -> coe
                    MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42
                    (coe d_inject_30 (coe v3) (coe v4))
             _ -> MAlonzo.RTE.mazUnreachableError
      MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v2 v3 v4
        -> coe
             (\ v5 v6 ->
                coe
                  MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                  (coe
                     d_inject_30 (coe v4) (coe v1 (d_forget_26 (coe v2) (coe v5)))))
      MAlonzo.Code.Once.Type.C_μ'45'type_132 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_ν'45'type_134 v2 -> coe v1
      MAlonzo.Code.Once.Type.C_Int_136 -> coe v1
      MAlonzo.Code.Once.Type.C_Float_138 -> coe v1
      MAlonzo.Code.Once.Type.C_Str_140 -> coe v1
      MAlonzo.Code.Once.Type.C_Buffer_142 -> coe v1
      _ -> MAlonzo.RTE.mazUnreachableError
-- Once.Denotation.DenotTrace.emit-D
d_emit'45'D_128 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_150 ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_emit'45'D_128 v0 ~v1 v2 v3 = du_emit'45'D_128 v0 v2 v3
du_emit'45'D_128 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.SigOp.Info.T_SigOpInfo_150 ->
  AgdaAny -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
du_emit'45'D_128 v0 v1 v2
  = let v3
          = MAlonzo.Code.Once.CCC.SigOp.Info.d_effect_166 (coe v1) in
    coe
      (case coe v3 of
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Pure_140
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Emits_142
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_152 (coe v0) (coe v1)
                   (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         MAlonzo.Code.Once.CCC.SigOp.Info.C_Halts_144
           -> coe
                MAlonzo.Code.Agda.Builtin.List.C__'8759'__22
                (coe
                   MAlonzo.Code.Once.Denotation.Trace.du_mkEvent_152 (coe v0) (coe v1)
                   (coe v2))
                (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16)
         _ -> MAlonzo.RTE.mazUnreachableError)
-- Once.Denotation.DenotTrace.evalᴰ
d_eval'7472'_154 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_eval'7472'_154 v0 v1 v2 v3
  = let v4
          = \ v4 ->
              coe
                MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                (coe
                   d_rec'45'trace'45'D_160 (coe v0) (coe v1) (coe v2)
                   (coe d_forget_26 (coe v0) (coe v3)) (coe v4))
                (coe
                   d_inject_30 (coe v1)
                   (coe
                      MAlonzo.Code.Once.CCC.Eval.d_eval_10 (coe v0) (coe v1) (coe v2)
                      (coe d_forget_26 (coe v0) (coe v3)))) in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.IR.C_id_280
           -> coe
                (\ v6 ->
                   coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12 (coe v3))
         MAlonzo.Code.Once.CCC.IR.C__'8728'__288 v6 v8 v9
           -> coe
                MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                (coe d_eval'7472'_154 (coe v0) (coe v6) (coe v9) (coe v3))
                (coe d_eval'7472'_154 (coe v6) (coe v1) (coe v8))
         MAlonzo.Code.Once.CCC.IR.C_'10216'_'44'_'10217'_296 v8 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'42'__126 v11 v12
                  -> coe
                       MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                       (coe d_eval'7472'_154 (coe v0) (coe v11) (coe v8) (coe v3))
                       (coe
                          (\ v13 ->
                             coe
                               MAlonzo.Code.Once.Denotation.TraceMonad.du__'62''62''61'T__20
                               (coe d_eval'7472'_154 (coe v0) (coe v12) (coe v9) (coe v3))
                               (coe
                                  (\ v14 v15 ->
                                     coe
                                       MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                                       (coe
                                          MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v13)
                                          (coe v14))))))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_fst_302
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'42'__126 v7 v8
                  -> coe
                       (\ v9 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v3)))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_snd_308
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'42'__126 v7 v8
                  -> coe
                       (\ v9 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3)))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_inl_314 v7
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 (coe v3)))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_inr_320 v7
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'43'__128 v8 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 (coe v3)))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_case_328 v8 v9
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'43'__128 v10 v11
                  -> case coe v3 of
                       MAlonzo.Code.Data.Sum.Base.C_inj'8321'_38 v12
                         -> coe d_eval'7472'_154 (coe v10) (coe v1) (coe v8) (coe v12)
                       MAlonzo.Code.Data.Sum.Base.C_inj'8322'_42 v12
                         -> coe d_eval'7472'_154 (coe v11) (coe v1) (coe v9) (coe v12)
                       _ -> MAlonzo.RTE.mazUnreachableError
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_terminal_332
           -> coe
                (\ v6 ->
                   coe
                     MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                     (coe MAlonzo.Code.Agda.Builtin.Unit.C_tt_8))
         MAlonzo.Code.Once.CCC.IR.C_curry_346 v9 v10
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
                  -> coe
                       (\ v14 ->
                          coe
                            MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12
                            (coe
                               (\ v15 ->
                                  d_eval'7472'_154
                                    (coe MAlonzo.Code.Once.Type.C__'42'__126 (coe v0) (coe v11))
                                    (coe v13) (coe v9)
                                    (coe
                                       MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32 (coe v3)
                                       (coe v15)))))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_apply_354
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'42'__126 v8 v9
                  -> case coe v8 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v10 v11 v12
                         -> coe
                              MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 v3
                              (MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v3))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_arr_362
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v8 v9 v10
                  -> case coe v1 of
                       MAlonzo.Code.Once.Type.C__'8658''91'_'93'__130 v11 v12 v13
                         -> coe
                              (\ v14 ->
                                 coe MAlonzo.Code.Once.Denotation.TraceMonad.du_returnT_12 (coe v3))
                       _ -> coe v4
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_Cata_376 v6 v8
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                               (coe
                                  MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v9 v6
                                  (d_cata'45'ev'45'alg'7472'_166
                                     (coe v9) (coe v1) (coe v10) (coe v8))
                                  (d_forget_26 (coe v0) (coe v3))))
                            (coe
                               d_inject_30 (coe v1)
                               (coe
                                  MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                                  (coe
                                     MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v9 v6
                                     (d_cata'45'ev'45'alg'7472'_166
                                        (coe v9) (coe v1) (coe v10) (coe v8))
                                     (d_forget_26 (coe v0) (coe v3))))))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_Ana_396 v6 v8
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_ν'45'type_134 v9
                  -> coe
                       (\ v10 ->
                          coe
                            MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                            (coe
                               d_ana'45'events_178 (coe v9) (coe v0) (coe v8)
                               (coe d_forget_26 (coe v0) (coe v3)) (coe v10))
                            (coe
                               d_inject_30 (coe v1)
                               (coe
                                  MAlonzo.Code.Once.Semantics.Core.du_sem'45'ana_1114 (coe v9)
                                  (coe
                                     (\ v11 ->
                                        coe
                                          MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108
                                          (coe v9)
                                          (coe
                                             d_forget_26
                                             (coe
                                                MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                (coe v9) (coe v0))
                                             (coe
                                                MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                                (coe
                                                   d_eval'7472'_154 (coe v0)
                                                   (coe
                                                      MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162
                                                      (coe v9) (coe v0))
                                                   (coe v8) (coe d_inject_30 (coe v0) (coe v11)))
                                                (coe (0 :: Integer))))))
                                  (coe d_forget_26 (coe v0) (coe v3)))))
                _ -> coe v4
         MAlonzo.Code.Once.CCC.IR.C_SigOp_424 v7
           -> coe
                (\ v8 ->
                   coe
                     MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                     (coe
                        du_emit'45'D_128 (coe v0) (coe v7)
                        (coe d_forget_26 (coe v0) (coe v3)))
                     (coe
                        d_inject_30 (coe v1)
                        (coe
                           MAlonzo.Code.Once.CCC.SigOp.Info.d_semM_164 v7
                           (d_forget_26 (coe v0) (coe v3)))))
         _ -> coe v4)
-- Once.Denotation.DenotTrace.rec-trace-D
d_rec'45'trace'45'D_160 ::
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_rec'45'trace'45'D_160 v0 v1 v2 v3 v4
  = let v5 = coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16 in
    coe
      (case coe v2 of
         MAlonzo.Code.Once.CCC.IR.C_In_366 v7 v8
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v9
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_out'45'μ_370 v7
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v8
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_Cata_376 v7 v9
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Core.du_sem'45'cata_954 v10 v7
                          (d_cata'45'ev'45'alg'7472'_166
                             (coe v10) (coe v1) (coe v4) (coe v9))
                          v3)
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_Para_382 v7 v9
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v10
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Core.du_sem'45'para_970 (coe v10)
                          (coe v7)
                          (coe
                             d_para'45'ev'45'alg'7472'_172 (coe v10) (coe v1) (coe v4) (coe v9))
                          (coe v3))
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_Out_386 v7
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_ν'45'type_134 v8
                  -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_Ana_396 v7 v9
           -> case coe v1 of
                MAlonzo.Code.Once.Type.C_ν'45'type_134 v10
                  -> coe
                       d_ana'45'events_178 (coe v10) (coe v0) (coe v9) (coe v3) (coe v4)
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_Hylo_404 v6 v8 v9 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v13
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat'45'events_1340
                          (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) v6 v13 v8 v9
                          (\ v14 v15 ->
                             coe
                               MAlonzo.Code.Once.CCC.Eval.du_appNatTr'45'F_18 (coe v13) (coe v6)
                               (coe v12) v15)
                          (\ v14 ->
                             coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                                  (coe
                                     d_eval'7472'_154
                                     (coe
                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                        (coe v1))
                                     (coe v1) (coe v11)
                                     (coe
                                        d_inject_30
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                                           (coe v6) (coe v14))))
                                  (coe v4))
                               (coe
                                  d_forget_26 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        d_eval'7472'_154
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                           (coe v1))
                                        (coe v1) (coe v11)
                                        (coe
                                           d_inject_30
                                           (coe
                                              MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                              (coe v1))
                                           (coe
                                              MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                                              (coe v6) (coe v14))))
                                     (coe v4))))
                          v3)
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_Fuse_412 v6 v8 v9 v11 v12
           -> case coe v0 of
                MAlonzo.Code.Once.Type.C_μ'45'type_132 v13
                  -> coe
                       MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                       (coe
                          MAlonzo.Code.Once.Semantics.Core.du_sem'45'fuseNat'45'events_1340
                          (coe MAlonzo.Code.Data.List.Base.du__'43''43'__32)
                          (coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16) v6 v13 v8 v9
                          (\ v14 v15 ->
                             coe
                               MAlonzo.Code.Once.CCC.Eval.du_appNatTr'45'F_18 (coe v13) (coe v6)
                               (coe v12) v15)
                          (\ v14 ->
                             coe
                               MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                               (coe
                                  MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                                  (coe
                                     d_eval'7472'_154
                                     (coe
                                        MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                        (coe v1))
                                     (coe v1) (coe v11)
                                     (coe
                                        d_inject_30
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                           (coe v1))
                                        (coe
                                           MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                                           (coe v6) (coe v14))))
                                  (coe v4))
                               (coe
                                  d_forget_26 (coe v1)
                                  (coe
                                     MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
                                     (coe
                                        d_eval'7472'_154
                                        (coe
                                           MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                           (coe v1))
                                        (coe v1) (coe v11)
                                        (coe
                                           d_inject_30
                                           (coe
                                              MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v6)
                                              (coe v1))
                                           (coe
                                              MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
                                              (coe v6) (coe v14))))
                                     (coe v4))))
                          v3)
                _ -> coe v5
         MAlonzo.Code.Once.CCC.IR.C_free'45'heap_414 v6
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         MAlonzo.Code.Once.CCC.IR.C_const_418 v7 v8 v9
           -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
         _ -> coe v5)
-- Once.Denotation.DenotTrace.cata-ev-algᴰ
d_cata'45'ev'45'alg'7472'_166 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_cata'45'ev'45'alg'7472'_166 v0 v1 v2 v3 v4
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
            (coe
               d_eval'7472'_154
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
               (coe v1) (coe v3)
               (coe
                  d_inject_30
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
                  (coe du_z_402 (coe v0) (coe v4))))
            (coe v2)))
      (coe
         d_forget_26 (coe v1)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe
               d_eval'7472'_154
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
               (coe v1) (coe v3)
               (coe
                  d_inject_30
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
                  (coe du_z_402 (coe v0) (coe v4))))
            (coe v2)))
-- Once.Denotation.DenotTrace.para-ev-algᴰ
d_para'45'ev'45'alg'7472'_172 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_para'45'ev'45'alg'7472'_172 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
      (coe
         MAlonzo.Code.Data.List.Base.du__'43''43'__32
         (coe
            MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
            (coe
               (\ v5 ->
                  MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v5))))
            (coe v4))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
            (coe
               d_eval'7472'_154
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0)
                  (coe
                     MAlonzo.Code.Once.Type.C__'42'__126
                     (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v1)))
               (coe v1) (coe v3)
               (coe
                  d_inject_30
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0)
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__126
                        (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v1)))
                  (coe du_z_418 (coe v0) (coe v4))))
            (coe v2)))
      (coe
         d_forget_26 (coe v1)
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe
               d_eval'7472'_154
               (coe
                  MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0)
                  (coe
                     MAlonzo.Code.Once.Type.C__'42'__126
                     (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v1)))
               (coe v1) (coe v3)
               (coe
                  d_inject_30
                  (coe
                     MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0)
                     (coe
                        MAlonzo.Code.Once.Type.C__'42'__126
                        (coe MAlonzo.Code.Once.Type.C_μ'45'type_132 (coe v0)) (coe v1)))
                  (coe du_z_418 (coe v0) (coe v4))))
            (coe v2)))
-- Once.Denotation.DenotTrace.ana-events
d_ana'45'events_178 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny ->
  Integer -> [MAlonzo.Code.Once.Denotation.Trace.T_SigOpEvent_136]
d_ana'45'events_178 v0 v1 v2 v3 v4
  = case coe v4 of
      0 -> coe MAlonzo.Code.Agda.Builtin.List.C_'91''93'_16
      _ -> let v5 = subInt (coe v4) (coe (1 :: Integer)) in
           coe
             (coe
                MAlonzo.Code.Data.List.Base.du__'43''43'__32
                (coe
                   MAlonzo.Code.Once.Denotation.TraceMonad.du_projTrace_62
                   (coe du_step_442 (coe v0) (coe v1) (coe v2) (coe v3)) (coe v5))
                (coe
                   MAlonzo.Code.Once.Denotation.TraceDenote.du_events'45'F_10 (coe v0)
                   (coe
                      (\ v6 ->
                         d_ana'45'events_178 (coe v0) (coe v1) (coe v2) (coe v6) (coe v5)))
                   (coe d_layer_444 (coe v0) (coe v1) (coe v2) (coe v3) (coe v5))))
-- Once.Denotation.DenotTrace._.z
d_z_402 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_274 -> AgdaAny -> AgdaAny
d_z_402 v0 ~v1 ~v2 ~v3 v4 = du_z_402 v0 v4
du_z_402 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_z_402 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 (coe v0)
         (coe (\ v2 -> MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))
         (coe v1))
-- Once.Denotation.DenotTrace._.z
d_z_418 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  Integer -> MAlonzo.Code.Once.CCC.IR.T_IR_274 -> AgdaAny -> AgdaAny
d_z_418 v0 ~v1 ~v2 ~v3 v4 = du_z_418 v0 v4
du_z_418 ::
  MAlonzo.Code.Once.Type.T_Functor_110 -> AgdaAny -> AgdaAny
du_z_418 v0 v1
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor'8315''185'_150
      (coe v0)
      (coe
         MAlonzo.Code.Once.Semantics.Core.du_sem'45'fmap_432 (coe v0)
         (coe
            (\ v2 ->
               coe
                 MAlonzo.Code.Agda.Builtin.Sigma.C__'44'__32
                 (coe MAlonzo.Code.Agda.Builtin.Sigma.d_fst_28 (coe v2))
                 (coe
                    MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30
                    (coe MAlonzo.Code.Agda.Builtin.Sigma.d_snd_30 (coe v2)))))
         (coe v1))
-- Once.Denotation.DenotTrace._.step
d_step_442 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny ->
  Integer -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
d_step_442 v0 v1 v2 v3 ~v4 = du_step_442 v0 v1 v2 v3
du_step_442 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 ->
  AgdaAny -> Integer -> MAlonzo.Code.Agda.Builtin.Sigma.T_Σ_14
du_step_442 v0 v1 v2 v3
  = coe
      d_eval'7472'_154 (coe v1)
      (coe
         MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
      (coe v2) (coe d_inject_30 (coe v1) (coe v3))
-- Once.Denotation.DenotTrace._.layer
d_layer_444 ::
  MAlonzo.Code.Once.Type.T_Functor_110 ->
  MAlonzo.Code.Once.Type.T_Type_112 ->
  MAlonzo.Code.Once.CCC.IR.T_IR_274 -> AgdaAny -> Integer -> AgdaAny
d_layer_444 v0 v1 v2 v3 v4
  = coe
      MAlonzo.Code.Once.Semantics.Core.du_coerce'45'functor_108 (coe v0)
      (coe
         d_forget_26
         (coe
            MAlonzo.Code.Once.Type.d_'10214'_'10215'T_162 (coe v0) (coe v1))
         (coe
            MAlonzo.Code.Once.Denotation.TraceMonad.du_valueT_70
            (coe du_step_442 (coe v0) (coe v1) (coe v2) (coe v3)) (coe v4)))
